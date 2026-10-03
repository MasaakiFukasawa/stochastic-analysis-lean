import Chapter4M2FinitePath
import Chapter4ThreeTermPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def stepTimePath (a b R : ℝ) : C(Icc (0:ℝ) R,ℝ) :=
  ⟨fun r => min b r.val-min a r.val,
    (continuous_const.min continuous_subtype_val).sub (continuous_const.min continuous_subtype_val)⟩

lemma step_drift_adapted
    {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (a b r : ℝ) (hab : a≤b) (G : Ω → ℝ) (hG : Measurable[F (realTimeClamp a)] G) :
    Measurable[F (realTimeClamp r)] (fun w => G w*(min b r-min a r)) := by
  by_cases har : a≤r
  · exact (hG.mono (hF (real_time_clamp_mono har)) le_rfl).mul_const _
  · have hra : r≤a := le_of_not_ge har
    simp only [min_eq_right hra,min_eq_right (hra.trans hab),sub_self,mul_zero]
    exact measurable_const

lemma random_step_path_measurable
    {Ω : Type*} [MeasurableSpace Ω] (G : Ω → ℝ) (hG : Measurable G) (a b R : ℝ) :
    Measurable (fun w => G w • stepTimePath a b R) := by
  exact hG.smul measurable_const

end Asakura.Chapter4
