import Chapter13BrownianParameterFubini
import Chapter2StoppingIntegrandMembership

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Stopping preserves the joint parameter/progressive measurability
required by stochastic Fubini, not only progressiveness for each parameter. -/
theorem parameter_stopping_progressive {Ω E:Type*} [MeasurableSpace E]
    (F:HalfClosedTime → MeasurableSpace Ω) (hF:Monotone F)
    (τ:Ω → HalfClosedTime) (hτ:∀t,MeasurableSet[F t] {w | τ w≤t})
    (b:ℝ) (H:E × (Ω × ℝ) → ℝ)
    (hp:@Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) => H (z.1,(z.2.1,z.2.2.val)))) :
    @Measurable _ _
      ((inferInstance : MeasurableSpace E).prod (progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val)))) inferInstance
      (fun z:E × (Ω × Icc (0:ℝ) b) =>
        (Ioc (⊥:HalfClosedTime) (τ z.2.1)).indicator (fun _ => H (z.1,(z.2.1,z.2.2.val))) (realTimeClamp z.2.2.val)) := by
  have hbot:∀t,MeasurableSet[F t] {w:Ω | (⊥:HalfClosedTime)≤t} := by simp
  have hi:=stopping_interval_prefix_progressive F hF (fun _ => ⊥) τ hbot hτ b
    (fun _ => (1:ℝ)) measurable_const
  letI:MeasurableSpace (Ω × Icc (0:ℝ) b):=progressiveSpace (fun t:Icc (0:ℝ) b => F (realTimeClamp t.val))
  have hh:=hp.mul (hi.comp measurable_snd)
  convert hh using 1
  funext z
  simp only [Pi.mul_apply,Function.comp_apply,indicator_apply]
  split_ifs <;> simp
end Asakura.Chapter13
#print axioms Asakura.Chapter13.parameter_stopping_progressive
