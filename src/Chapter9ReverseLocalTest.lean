import Chapter9ReverseBoundedTest
import Chapter9CompactTestLocalization
open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem ou_reverse_local_smooth_test {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXc : ∀ w,Continuous (fun r => X r w)) (T : ℝ)
    (hCE : ∀ a b,0≤a → a<b → b<T → ∀ g,IsBoundedBorel g →
      P[(fun w => g (X (T-b) w))|reversedNaturalInformation P X T a]=ᵐ[P]
        (fun w => ouReverseParamTransition μ T a (fun z => g z.2) (b,X (T-a) w)))
    (q : (Fin d → ℝ) → ℝ) (hq : ContDiff ℝ ∞ q)
    (b : ℝ) (hb : 0≤b) (hbT : b<T) :
    LocalMProcessWitness P
      (fun (t : HalfClosedTime) => reversedNaturalInformation P X T (finitePrefixTime b hb t).val)
      (fun t w => reverseCompensated μ T (fun r => X (T-r)) q
        (finitePrefixTime b hb t).val w) := by
  apply compact_test_localization P μ T b hb _
    ((reversed_information_monotone P X T).comp (fun s t hst => finite_prefix_time_mono b hb hst))
    (fun t => reversed_information_le P X hXm T _) (fun r => X (T-r))
  · intro t
    exact reversed_state_adapted P X T _ (finitePrefixTime b hb t).property.1
  · intro w
    exact (hXc w).comp (continuous_const.sub
      (continuous_subtype_val.comp (finite_prefix_time_continuous b hb)))
  · intro f hf hfc
    simpa only [reverseCompensated,sub_zero] using!
      ou_reverse_test_bounded_process P μ X hXm hXc T hCE f hf hfc b hb hbT
  · exact hq
end Asakura.Chapter9
