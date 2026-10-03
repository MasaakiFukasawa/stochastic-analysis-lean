import Chapter4PathMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

lemma paths_equal_of_zero_second_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (Y Z : Ω → E) (hi : MemLp (fun w => Y w-Z w) 2 P)
    (hz : (∫ w,‖Y w-Z w‖^2 ∂P)=0) : Y=ᵐ[P] Z := by
  have hlp : eLpNorm (fun w => Y w-Z w) 2 P=0 := by
    rw [path_eLpNorm_eq_sqrt_moment P (fun w => Y w-Z w) hi,hz,Real.sqrt_zero,ENNReal.ofReal_zero]
  have h := (eLpNorm_eq_zero_iff (by norm_num : (2:ℝ≥0∞)≠0)).1 hlp
  filter_upwards [h] with w hw
  exact sub_eq_zero.mp hw

end Asakura.Chapter4
