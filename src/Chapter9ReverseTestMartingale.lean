import Chapter9CompensatedMartingale
import Chapter9ReverseTestIncrement

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's full test-function martingale, without assuming
 integrability or adaptedness of its compensating time integral. -/
theorem ou_reverse_test_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXc : ∀ w,Continuous (fun r => X r w)) (T : ℝ)
    (hCE : ∀ a b,0≤a → a<b → b<T → ∀ g,IsBoundedBorel g →
      P[(fun w => g (X (T-b) w))|reversedNaturalInformation P X T a]=ᵐ[P]
        (fun w => ouReverseParamTransition μ T a (fun z => g z.2) (b,X (T-a) w)))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (s t : ℝ) (hs : 0≤s) (hst : s≤t) (htT : t<T) :
    P[(fun w => f (X (T-t) w)-f (X T w)-
      ∫ r in 0..t,ouReverseGenerator μ f (T-r,X (T-r) w))|
        reversedNaturalInformation P X T s]=ᵐ[P]
      (fun w => f (X (T-s) w)-f (X T w)-
        ∫ r in 0..s,ouReverseGenerator μ f (T-r,X (T-r) w)) := by
  have ht : 0≤t := hs.trans hst
  have hj : Measurable (fun z : ℝ × Ω => X z.1 z.2) :=
    measurable_uncurry_of_continuous_of_measurable hXc hXm
  have hgm := ou_reverse_generator_measurable μ f hf
  have hfb : IsBoundedBorel f := by
    obtain ⟨D,hD⟩ := hfc.exists_bound_of_continuous hf.continuous
    exact ⟨hf.continuous.measurable,max D 0,le_max_right _ _,fun y => (hD y).trans (le_max_left _ _)⟩
  obtain ⟨C,_,hC⟩ := ou_reverse_generator_bound μ f hf hfc (T-t) T (by linarith)
  have he := compensated_process_martingale P (reversedNaturalInformation P X T)
    (reversed_information_monotone P X T) (reversed_information_le P X hXm T)
    (fun r w => f (X (T-r) w)) (fun r w => ouReverseGenerator μ f (T-r,X (T-r) w))
    t ht
    (fun r hr => hf.continuous.measurable.comp (reversed_state_adapted P X T r hr.1))
    (fun r _ => (hfb.comp _ (hXm _)).integrable P)
    (fun r hr => hgm.comp (measurable_const.prodMk (reversed_state_adapted P X T r hr.1)))
    (fun w => (ou_reverse_generator_continuous μ f hf).comp
      ((show Continuous (fun r : ℝ => T-r) by fun_prop).prodMk
        ((hXc w).comp (by fun_prop))).continuousOn
      (fun r hr => ⟨show 0<T-r from sub_pos.mpr (hr.2.trans_lt htT),mem_univ _⟩))
    (hgm.comp ((measurable_const.sub measurable_fst).prodMk
      (hj.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd))))
    C (fun r hr w => hC _ ⟨by linarith [hr.2],by linarith [hr.1]⟩ _)
    (fun a b ha hab hbt => ou_reverse_test_increment P μ X hXm hj T hCE f hf hfc
      a b ha hab (hbt.trans_lt htT)) s t hs hst le_rfl
  simpa only [sub_zero] using he
end Asakura.Chapter9
