import Chapter10CompletedIndependence
import Chapter10ConditionalCovariance

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Identification with the manuscript's completed observation information.
The final assertion identifies the whole conditional law of the residual,
not only its first two moments, and allows singular covariance matrices. -/
theorem completed_filter_identification {Ω U V : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (Y : Ω → U) (I : Ω → V) (hY : Measurable Y) (hI : Measurable I)
    (e a : Ω → Fin d → ℝ) (he : Measurable e) (hg : HasGaussianLaw e P)
    (hind : IndepFun e I P)
    (hinfo : nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)=
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap I inferInstance))
    (ha : Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap Y inferInstance)] a)
    (hia : ∀ i,Integrable (fun w => a w i) P)
    (hzero : ∀ i,∫ w,e w i ∂P=0) :
    let H := nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)
    (∀ i,P[(fun w => a w i+e w i)|H]=ᵐ[P] (fun w => a w i)) ∧
    (∀ i j,P[(fun w => e w i*e w j)|H]=ᵐ[P] (fun _ => ∫ w,e w i*e w j ∂P)) ∧
    (∀ f : (Fin d → ℝ) → ℝ,Measurable f →
      P[(f ∘ e)|H]=ᵐ[P] (fun _ => ∫ w,f (e w) ∂P)) := by
  letI : MeasurableSpace Ω := mΩ
  let H := nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)
  have hH : H≤mΩ := null_augmented_le (m := mΩ) P _ hY.comap_le
  have hInd : Indep (MeasurableSpace.comap e inferInstance) H P := by
    dsimp only [H]
    rw [hinfo]
    exact independent_completed_history (m := mΩ) P _ _ he.comap_le hI.comap_le hind
  refine ⟨?_,independent_error_conditional_covariance P H hH e he hInd,?_⟩
  · intro i
    have hi := (hg.eval i).integrable
    have hm : Measurable[MeasurableSpace.comap e inferInstance] e :=
      Measurable.of_comap_le le_rfl
    have hce := condExp_indep_eq he.comap_le hH
      (((measurable_pi_apply i).comp hm).stronglyMeasurable) hInd
    have hself := condExp_of_stronglyMeasurable hH
      (((measurable_pi_apply i).comp ha).stronglyMeasurable) (hia i)
    have hselfi : P[(fun w => a w i)|H]=(fun w => a w i) := hself
    have hcei : P[(fun w => e w i)|H]=ᵐ[P] (fun _ => (0:ℝ)) := by
      simpa only [Function.comp_def,hzero] using! hce
    have hadd := condExp_add (hia i) hi H
    filter_upwards [hcei,hadd] with w hw hwadd
    change P[(fun w => a w i+e w i)|H] w=a w i
    simpa only [Pi.add_apply,hselfi,hw,add_zero] using! hwadd
  · intro f hf
    exact independent_error_conditional_test P H hH e he hInd f hf

end Asakura.Chapter10
