import Chapter9BoundedCompensatedProcess
import Chapter9ReverseTestIncrement
open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem ou_reverse_test_bounded_process {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXc : ∀ w,Continuous (fun r => X r w)) (T : ℝ)
    (hCE : ∀ a b,0≤a → a<b → b<T → ∀ g,IsBoundedBorel g →
      P[(fun w => g (X (T-b) w))|reversedNaturalInformation P X T a]=ᵐ[P]
        (fun w => ouReverseParamTransition μ T a (fun z => g z.2) (b,X (T-a) w)))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (b : ℝ) (hb : 0≤b) (hbT : b<T) :
    (fun (t : HalfClosedTime) w =>
      f (X (T-(finitePrefixTime b hb t).val) w)-f (X T w)-
        ∫ r in 0..(finitePrefixTime b hb t).val,ouReverseGenerator μ f (T-r,X (T-r) w)) ∈
      boundedMProcess P (fun t => reversedNaturalInformation P X T (finitePrefixTime b hb t).val) := by
  have hj : Measurable (fun z : ℝ × Ω => X z.1 z.2) :=
    measurable_uncurry_of_continuous_of_measurable hXc hXm
  have hgm := ou_reverse_generator_measurable μ f hf
  obtain ⟨D,hD⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨C,hC0,hC⟩ := ou_reverse_generator_bound μ f hf hfc (T-b) T (by linarith)
  have he := bounded_compensated_process P (reversedNaturalInformation P X T)
    (reversed_information_monotone P X T) (reversed_information_le P X hXm T)
    (fun r w => f (X (T-r) w)) (fun r w => ouReverseGenerator μ f (T-r,X (T-r) w)) b hb
    (fun r hr => hf.continuous.measurable.comp (reversed_state_adapted P X T r hr.1))
    (fun w => (hf.continuous.comp ((hXc w).comp (by fun_prop))).continuousOn)
    D (fun r _ w => hD (X (T-r) w))
    (fun r hr => hgm.comp (measurable_const.prodMk (reversed_state_adapted P X T r hr.1)))
    (fun w => (ou_reverse_generator_continuous μ f hf).comp
      ((show Continuous (fun r : ℝ => T-r) by fun_prop).prodMk
        ((hXc w).comp (by fun_prop))).continuousOn
      (fun r hr => ⟨show 0<T-r from sub_pos.mpr (hr.2.trans_lt hbT),mem_univ _⟩))
    (hgm.comp ((measurable_const.sub measurable_fst).prodMk
      (hj.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd))))
    C hC0 (fun r hr w => hC _ ⟨by linarith [hr.2],by linarith [hr.1]⟩ _)
    (fun a c ha hac hcb => ou_reverse_test_increment P μ X hXm hj T hCE f hf hfc
      a c ha hac (hcb.trans_lt hbT))
  simpa only [sub_zero] using he
end Asakura.Chapter9
