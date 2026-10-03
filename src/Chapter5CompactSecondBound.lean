import Chapter5SmoothCylinderBounds
namespace Asakura.Chapter5
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem compact_second_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ) (hc : Continuous DD) (hs : HasCompactSupport DD) :
    ∃ K : ℝ,∀ x,‖DD x‖≤K := by
  letI : SeminormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toSeminormedAddCommGroup
  exact hs.exists_bound_of_continuous hc
end Asakura.Chapter5
