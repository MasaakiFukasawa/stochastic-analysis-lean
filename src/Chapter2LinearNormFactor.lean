import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Module.Basic

namespace Asakura.Chapter2Complete
set_option maxHeartbeats 900000

/-- Equal seminorms imply that a linear map descends to the normed range of
the comparison map. This is the representative-independence step for Ito. -/
theorem linear_isometry_factor_through_range
    {E F G : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : E →ₗ[ℝ] F) (J : E →ₗ[ℝ] G) (hnorm : ∀ x, ‖J x‖ = ‖K x‖) :
    ∃ L : K.range →ₗᵢ[ℝ] G, ∀ x, L ⟨K x,LinearMap.mem_range_self K x⟩ = J x := by
  have hker : K.ker ≤ J.ker := by
    intro x hx
    change J x = 0
    apply norm_eq_zero.mp
    rw [hnorm,show K x = 0 from hx,norm_zero]
  let L := (K.ker.liftQ J hker).comp K.quotKerEquivRange.symm.toLinearMap
  have he x (hx : K x ∈ K.range) : L ⟨K x,hx⟩ = J x := by
    dsimp only [L,LinearMap.comp_apply,LinearEquiv.coe_coe]
    rw [K.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨⟨L,?_⟩,fun x => he x _⟩
  intro y
  obtain ⟨x,hx⟩ := y.property
  have hy : y = ⟨K x,LinearMap.mem_range_self K x⟩ := Subtype.ext hx.symm
  rw [hy,he]
  exact hnorm x

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.linear_isometry_factor_through_range
