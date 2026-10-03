import Chapter12VectorCylinderRebasis
import Chapter12VectorHigherCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

noncomputable def finiteVectorCylinderExpr {H E : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {q : ℕ}
    (c : Fin q → SmoothCylinder H) (v : Fin q → E) : VectorCylinderExpr H E :=
  .sum q (fun j => .term (c j) (v j))

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

theorem finite_vector_expr_coe {q : ℕ} (c : Fin q → SmoothCylinder H) (v : Fin q → H)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) :
    ((finiteVectorCylinderExpr c v).valueLp P W S hS hcore p hp : Ω → H)=ᵐ[P]
      (fun w => ∑ j,(c j).value P W w • v j) := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j => vectorCylinderValue P W S hS hcore (c j) (v j) p hp),
    ae_all_iff.mpr (fun j => vector_cylinder_value_coe H P W S hS hcore p hp (c j) (v j))] with w hw hj
  change (∑ j,vectorCylinderValue P W S hS hcore (c j) (v j) p hp) w=_
  rw [hw]
  exact Finset.sum_congr rfl (fun j _ => hj j)

/-- One and the same orthonormal representation works at every Lp exponent,
which is needed to combine an Lp estimate with the L2 adjoint definition. -/
theorem finite_vector_core_rebasis {q : ℕ} (c : Fin q → SmoothCylinder H) (v : Fin q → H) :
    ∃ (n : ℕ) (e : Fin (n+1) → H) (u : Fin (n+1) → GaussianJet (n+1)),
      Orthonormal ℝ e ∧ ∀ (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤),
        (finiteVectorCylinderExpr c v).valueLp P W S hS hcore p hp=
          gaussianTensorCore H P W S hS hcore p hp u e 0 := by
  obtain ⟨n,e,u,he,hrep⟩ := finite_vector_cylinder_orthonormal_representation P W c v
  refine ⟨n,e,u,he,fun p _ hp => ?_⟩
  apply Lp.ext
  filter_upwards [finite_vector_expr_coe H P W S hS hcore c v p hp,hrep,
    gaussian_tensor_core_coe H P W S hS hcore p hp u e 0] with w hw hr hg
  rw [hw,hr,hg]
  exact (Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin (n+1)))
    (fun i => (u i).f (fun j => W (e j) w) • e i)).symm

theorem vector_rebasis_all_derivatives (c : VectorCylinderExpr H H)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (D : ∀ k : ℕ,Lp (positiveMalliavinTensorPower H k) p P →ₗ.[ℝ]
      Lp (positiveMalliavinTensorPower H (k+1)) p P)
    (hD : ∀ k (a : VectorCylinderExpr H (positiveMalliavinTensorPower H k)),
      (a.valueLp P W S hS hcore p hp,a.differentiate.valueLp P W S hS hcore p hp)∈(D k).graph)
    {N : ℕ} (u : Fin N → GaussianJet N) (e : Fin N → H)
    (h0 : c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0) :
    ∀ k,(iteratedVectorCylinderExpr H c k).valueLp P W S hS hcore p hp=
      gaussianTensorCore H P W S hS hcore p hp u e k := by
  apply closed_jet_all_orders_unique (fun k => Lp (positiveMalliavinTensorPower H k) p P) D
    (fun k => (iteratedVectorCylinderExpr H c k).valueLp P W S hS hcore p hp)
    (fun k => gaussianTensorCore H P W S hS hcore p hp u e k)
  · intro k
    exact hD k (iteratedVectorCylinderExpr H c k)
  · intro k
    apply gaussian_tensor_core_graph H P W S hS hcore p hp u e k (D k)
    intro a v
    simpa only [vector_cylinder_differentiate_value,VectorCylinderExpr.valueLp,
      VectorCylinderExpr.gradientLp] using hD k (.term a v)
  · exact h0

end Asakura.Chapter12
