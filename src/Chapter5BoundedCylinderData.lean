import Chapter5SmoothCylinderData

open scoped NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The revised representation lemma assumes bounded first and second
 derivatives, not compact support or a bounded payoff. -/
theorem bounded_C2_cylinder_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (C K : ℝ≥0) (hC : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hK : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K) :
    ∃ u : SmoothCylinderData E, u.value=f := by
  have hD : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact ⟨{
    value := f
    first := fderiv ℝ f
    second := fderiv ℝ (fderiv ℝ f)
    firstBound := C
    secondBound := K
    derivative := fun x => (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    secondDerivative := fun x => (hD.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    firstContinuous := hf.continuous_fderiv (by norm_num)
    secondContinuous := hD.continuous_fderiv (by norm_num)
    first_le := hC
    second_le := hK },rfl⟩

end Asakura.Chapter5
