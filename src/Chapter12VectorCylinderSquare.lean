import Chapter12VectorExprFamilyRebasis
import Chapter12GaussianVectorNormSquare

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)

theorem gaussian_tensor_core_zero_coe {N:ℕ} (u:Fin N → GaussianJet N) (e:Fin N → H)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤) :
    (gaussianTensorCore H P W S hS hcore p hp u e 0 : Ω → H)=ᵐ[P]
      (fun w => gaussianVectorFunction u e (fun i => W (e i) w)) := by
  filter_upwards [gaussian_tensor_core_coe H P W S hS hcore p hp u e 0] with w hw
  rw [hw]
  exact Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin N))
    (fun i => (u i).f (fun j => W (e j) w) • e i)

theorem vector_rebased_raw_value (c:VectorCylinderExpr H H)
    {N:ℕ} (u:Fin N → GaussianJet N) (e:Fin N → H)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
    (hc:c.valueLp P W S hS hcore p hp=gaussianTensorCore H P W S hS hcore p hp u e 0) :
    c.rawValue P W=ᵐ[P] (fun w => gaussianVectorFunction u e (fun i => W (e i) w)) := by
  have hh := c.valueLp_coe H P W S hS hcore p hp
  rw [hc] at hh
  exact hh.symm.trans (gaussian_tensor_core_zero_coe H P W S hS hcore u e p hp)

include hcore hS

theorem vector_cylinder_square_exists (c:VectorCylinderExpr H H) :
    ∃f:SmoothCylinder H,f.value P W=ᵐ[P] (fun w => ‖c.rawValue P W w‖^2) := by
  obtain ⟨n,e,u,he,hu⟩ := vector_expr_family_rebasis H P W S hS hcore (fun _:Fin 1 => c)
  have hc := vector_rebased_raw_value H P W S hS hcore c (u 0) e 2 (by simp) (hu 0 2 (by simp))
  refine ⟨(gaussianVectorNormSquare (u 0)).toCylinder e,?_⟩
  filter_upwards [hc] with w hw
  change (gaussianVectorNormSquare (u 0)).f (fun i => W (e i) w)=_
  rw [gaussianVectorNormSquare_value (u 0) e he,Function.comp_apply,←hw]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_cylinder_square_exists
