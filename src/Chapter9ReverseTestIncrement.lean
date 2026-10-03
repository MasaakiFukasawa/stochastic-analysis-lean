import Chapter9ReverseTransitionIdentity
import Chapter9CompensatedConditionalIncrement
import Chapter9BoundedTests

open MeasureTheory Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Conditional zero-mean generator increments, with all drift integrability
 and conditional integral exchange derived from compact support. -/
theorem ou_reverse_test_increment {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → Fin d → ℝ) (hXm : ∀ r,Measurable (X r))
    (hXjoint : Measurable (fun z : ℝ × Ω => X z.1 z.2))
    (T : ℝ)
    (hCE : ∀ a b,0≤a → a<b → b<T → ∀ g,IsBoundedBorel g →
      P[(fun w => g (X (T-b) w))|reversedNaturalInformation P X T a]=ᵐ[P]
        (fun w => ouReverseParamTransition μ T a (fun z => g z.2) (b,X (T-a) w)))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (s t : ℝ) (hs : 0≤s) (hst : s<t) (htT : t<T) :
    P[(fun w => f (X (T-t) w)-
      ∫ h,ouReverseGenerator μ f (T-(s+h),X (T-(s+h)) w)
        ∂volume.restrict (Ioc 0 (t-s)))|reversedNaturalInformation P X T s]=ᵐ[P]
      (fun w => f (X (T-s) w)) := by
  let F := reversedNaturalInformation P X T s
  let ρ := volume.restrict (Ioc 0 (t-s))
  let g := fun z : ℝ × (Fin d → ℝ) => ouReverseGenerator μ f (T-z.1,z.2)
  let H := fun z : Ω × ℝ => g (s+z.2,X (T-(s+z.2)) z.1)
  let K := fun z : Ω × ℝ => ouReverseParamTransition μ T s g (s+z.2,X (T-s) z.1)
  letI : MeasurableSpace Ω := m
  have hg : Measurable g := (ou_reverse_generator_measurable μ f hf).comp (by fun_prop)
  have hp := ou_reverse_param_transition_measurable μ T s g hg
  have hH : Measurable H := hg.comp ((measurable_const.add measurable_snd).prodMk
    (hXjoint.comp ((measurable_const.sub (measurable_const.add measurable_snd)).prodMk measurable_fst)))
  have hK : Measurable K := hp.comp ((measurable_const.add measurable_snd).prodMk
    ((hXm (T-s)).comp measurable_fst))
  have hle : F≤m := reversed_information_le P X hXm T s
  have hmi : AEStronglyMeasurable[F] (fun w => ∫ h,K (w,h) ∂ρ) P := by
    have hm : Measurable (fun z : (Fin d → ℝ) × ℝ =>
      ouReverseParamTransition μ T s g (s+z.2,z.1)) := hp.comp (by fun_prop)
    exact (hm.stronglyMeasurable.integral_prod_right'.measurable.comp
      (reversed_state_adapted P X T s hs)).aestronglyMeasurable
  obtain ⟨C,hC,hbound⟩ := ou_reverse_generator_bound μ f hf hfc (T-t) T (by linarith)
  have hb : ∀ᵐ h ∂ρ,∀ᵐ w ∂P,‖H (w,h)‖≤C := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with h hh
    exact ae_of_all _ (fun w => hbound _ ⟨by linarith [hh.2],by linarith [hh.1]⟩ _)
  have he : ∀ᵐ h ∂ρ,P[(fun w => H (w,h))|F]=ᵐ[P] (fun w => K (w,h)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with h hh
    have hgb : IsBoundedBorel (fun y => g (s+h,y)) :=
      ⟨hg.comp (by fun_prop),C,hC,fun y => hbound _ ⟨by linarith [hh.2],by linarith [hh.1]⟩ y⟩
    exact hCE s (s+h) hs (by linarith [hh.1]) (by linarith [hh.2]) _ hgb
  have hfb : IsBoundedBorel f := by
    obtain ⟨D,hD⟩ := hfc.exists_bound_of_continuous hf.continuous
    exact ⟨hf.continuous.measurable,max D 0,le_max_right _ _,fun y => (hD y).trans (le_max_left _ _)⟩
  have htrans : P[(fun w => f (X (T-t) w))|F]=ᵐ[P]
      (fun w => f (X (T-s) w)+∫ h,K (w,h) ∂ρ) := by
    filter_upwards [hCE s t hs hst htT f hfb] with w hw
    rw [hw]
    exact ou_reverse_transition_identity μ f hf hfc T s t hst htT (X (T-s) w)
  exact compensated_conditional_increment P ρ H K hH hK C hb F hle hmi he
    (fun w => f (X (T-t) w)) (fun w => f (X (T-s) w))
    ((hfb.comp _ (hXm _)).integrable P) htrans
end Asakura.Chapter9
