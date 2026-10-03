import Chapter10ConditionalCovariance

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false

/-- Given the joint Gaussianity and cross-moments computed by Ito's formula,
identify the proposed estimate and its conditional covariance using the full
observation history, not a finite-time surrogate. -/
theorem gaussian_filter_identification {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (e m : Ω → Fin d → ℝ) (I : ι → Ω → ℝ)
    (he : Measurable e) (hI : ∀ i, Measurable (I i))
    (hg : ∀ J : Finset ι,
      HasGaussianLaw (fun w => (e w,fun j : J => I j.val w)) P)
    (hc : ∀ i j,cov[(fun w => e w i),I j;P]=0)
    (hm : Measurable[MeasurableSpace.comap (fun w i => I i w) inferInstance] m)
    (him : ∀ i, Integrable (fun w => m w i) P)
    (hz : ∀ i, ∫ w,e w i ∂P=0) :
    let G := MeasurableSpace.comap (fun w i => I i w) inferInstance
    (∀ i, P[(fun w => m w i+e w i) | G] =ᵐ[P] (fun w => m w i)) ∧
    (∀ i j,P[(fun w => e w i*e w j) | G] =ᵐ[P]
      (fun _ => ∫ w,e w i*e w j ∂P)) := by
  let G := MeasurableSpace.comap (fun w i => I i w) inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hG : G≤mΩ := (Measurable.of_eval hI).comap_le
  have hind := gaussian_error_independent_history P e I he hI hg hc
  constructor
  · intro i
    have hei : Integrable (fun w => e w i) P := ((hg ∅).fst.eval i).integrable
    have hce := condExp_indep_eq he.comap_le hG
      (((measurable_pi_apply i).comp
        (show Measurable[MeasurableSpace.comap e inferInstance] e from
          Measurable.of_comap_le le_rfl)).stronglyMeasurable) hind
    have hself := condExp_of_stronglyMeasurable hG
      (((measurable_pi_apply i).comp hm).stronglyMeasurable) (him i)
    have hs := condExp_add (him i) hei G
    have hselfi : P[(fun w => m w i) | G] = (fun w => m w i) := hself
    have hcei : P[(fun w => e w i) | G] =ᵐ[P] (fun _ => (0:ℝ)) := by
      simpa only [Function.comp_def,hz] using! hce
    filter_upwards [hcei,hs] with w hw hs
    change P[(fun w => m w i+e w i) | G] w = m w i
    simpa only [Pi.add_apply,hselfi,hw,add_zero] using! hs
  · exact independent_error_conditional_covariance P G hG e he hind

end Asakura.Chapter10
