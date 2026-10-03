import Chapter12VectorCylinderFiniteSum
import Chapter12GaussianJetSquareBound

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

variable {Ω : Type*} [MeasurableSpace Ω] (H : RealHilbertSpaceData) [Nontrivial H]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
  (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)

theorem vector_expr_core_rebasis (c : VectorCylinderExpr H H) :
    ∃ (n : ℕ) (e : Fin (n+1) → H) (u : Fin (n+1) → GaussianJet (n+1)),
      Orthonormal ℝ e ∧ ∀ (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤),
        c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0 := by
  obtain ⟨n,e,u,he,hrep⟩ := finite_vector_core_rebasis H P W S hS hcore
    (fun j : Fin c.finiteTerms.length => (c.finiteTerms.get j).1)
    (fun j => (c.finiteTerms.get j).2)
  refine ⟨n,e,u,he,fun p _ hp => ?_⟩
  rw [vector_expr_finite_sum H P W S hS hcore p hp c]
  exact hrep p hp

/-- The original square estimate on the entire vector cylinder core,
with its actual closed-derivative adjoint and only one derivative norm. -/
theorem vector_cylinder_divergence_square_bound
    (D₀ : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D₀.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore 2 (by simp)))
    (c : VectorCylinderExpr H H) :
    ∃ g : SmoothCylinder H,
      IsDivergence D₀ (c.valueLp P W S hS hcore 2 (by simp))
        (g.valueLp P W S hS hcore 2 (by simp)) ∧
      ‖g.valueLp P W S hS hcore 2 (by simp)‖^2≤
        ‖c.valueLp P W S hS hcore 2 (by simp)‖^2+
        ‖c.differentiate.valueLp P W S hS hcore 2 (by simp)‖^2 := by
  obtain ⟨n,e,u,he,hrep⟩ := vector_expr_core_rebasis H P W S hS hcore c
  obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore 2 2 (by simp) (by simp) hdense
  have ho := vector_rebasis_all_derivatives H P W S hS hcore c 2 (by simp) D hD u e (hrep 2 (by simp))
  refine ⟨(GaussianJet.divergence u).toCylinder e,?_,?_⟩
  · rw [hrep 2 (by simp)]
    exact gaussian_core_is_divergence H P W S hS hcore u e he D₀ hgraph
  · have h0 := ho 0
    have h1 := ho 1
    change c.valueLp P W S hS hcore 2 (by simp)=_ at h0
    change c.differentiate.valueLp P W S hS hcore 2 (by simp)=_ at h1
    rw [h0,h1]
    exact gaussian_core_square_bound H P W S hS hcore u e he

end Asakura.Chapter12
