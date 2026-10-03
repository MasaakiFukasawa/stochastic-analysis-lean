import Chapter9ContinuousDriftVariation
import Chapter2SemimartingaleDecomposition

open MeasureTheory Set
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem finite_drift_semimartingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (Z a : ℝ → Ω → ℝ) (b : ℝ) (hb : 0≤b)
    (hZ0 : Measurable[F ⊥] (Z 0))
    (hZc : ∀ w,ContinuousOn (fun r => Z r w) (Icc 0 b))
    (ha : ∀ r∈Icc 0 b,Measurable[F (realTimeClamp r)] (a r))
    (hac : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 b))
    (hM : LocalMProcessWitness P F (fun t w =>
      Z (finitePrefixTime b hb t).val w-Z 0 w-∫ r in 0..(finitePrefixTime b hb t).val,a r w)) :
    SemimartingaleDecomposition P F
      (fun t w => Z (finitePrefixTime b hb t).val w)
      (fun t w => Z 0 w+∫ r in 0..(finitePrefixTime b hb t).val,a r w)
      (fun t w => Z (finitePrefixTime b hb t).val w-Z 0 w-∫ r in 0..(finitePrefixTime b hb t).val,a r w) := by
  refine ⟨continuous_drift_variation F hF a (Z 0) hZ0 b hb ha hac,hM,?_,?_⟩
  · intro w t _
    exact ((hZc w).comp_continuous
      (continuous_subtype_val.comp (finite_prefix_time_continuous b hb))
      (fun u => (finitePrefixTime b hb u).property)).continuousAt
  · intro t _ w
    ring
end Asakura.Chapter9
