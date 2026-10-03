import Chapter5SmoothCylinderData
import Chapter5CompactSecondBound

namespace Asakura.Chapter5
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true

private theorem compact_seminorm_bound {E G : Type*} [TopologicalSpace E]
    [SeminormedAddGroup G] (g : E → G) (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ B : ℝ,∀ x,‖g x‖≤B := hs.exists_bound_of_continuous hg

/-- The compactly supported C² approximants of the representation theorem
supply all the actual bounded derivative data required by the recursion. -/
theorem compact_cylinder_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ u : SmoothCylinderData E,u.value=f := by
  let D : E → E →L[ℝ] ℝ := fderiv ℝ f
  let DD : E → E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ D
  have hD1 : ContDiff ℝ 1 D := hf.fderiv_right (by norm_num)
  have hd x : HasFDerivAt f (D x) x := (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hdd x : HasFDerivAt D (DD x) x := (hD1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hDc : Continuous D := hf.continuous_fderiv (by norm_num)
  have hDDc : Continuous DD := hD1.continuous_fderiv (by norm_num)
  obtain ⟨hsD,hsDD⟩ := smooth_compact_cylinder_derivatives_support f D DD hd hdd hs
  obtain ⟨C,hC⟩ := compact_seminorm_bound D hDc hsD
  obtain ⟨K,hK⟩ := compact_second_derivative_bound DD hDDc hsDD
  have hC0 : 0≤C := (norm_nonneg (D 0)).trans (hC 0)
  have hK0 : 0≤K := (norm_nonneg (DD 0)).trans (hK 0)
  exact ⟨{
    value := f
    first := D
    second := DD
    firstBound := ⟨C,hC0⟩
    secondBound := ⟨K,hK0⟩
    derivative := hd
    secondDerivative := hdd
    firstContinuous := hDc
    secondContinuous := hDDc
    first_le := hC
    second_le := hK },rfl⟩

end Asakura.Chapter5
