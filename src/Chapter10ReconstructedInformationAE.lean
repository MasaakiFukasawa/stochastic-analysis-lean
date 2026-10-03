import Chapter10DriftHistoryMeasurable
import Chapter10ReconstructedInformation
import Chapter10LinearReconstructionAE
import Chapter10CompletedIndependence

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The four reconstruction equations in the filtering proof imply equality
of completed information. The measurability premises here concern only the
deterministic coefficient stochastic integrals, supplied separately by their
actual discrete approximation theorem. -/
theorem reconstructed_observation_information_ae {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {d r : ℕ} (T : ℝ) (hT : 0≤T)
    (Y I : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (m ZKY ZKDI : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (ZJY ZDI : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (hYm : Measurable[mΩ] Y) (hIm : Measurable[mΩ] I) (hmm : Measurable[mΩ] m)
    (m0 : Fin d → ℝ)
    (F A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (JC C : ℝ → (Fin d → ℝ) →L[ℝ] (Fin r → ℝ))
    (hF : Continuous F) (hA : Continuous A) (hJC : Continuous JC) (hC : Continuous C)
    (hKY : Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap Y inferInstance)] ZKY)
    (hJY : Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap Y inferInstance)] ZJY)
    (hKDI : Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap I inferInstance)] ZKDI)
    (hDI : Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap I inferInstance)] ZDI)
    (hmY : ∀ᵐ w ∂P,∀ t,m w t=m0+(∫ s in 0..t.val,F s (m w (projIcc 0 T hT s)))+ZKY w t)
    (hI : ∀ᵐ w ∂P,∀ t,I w t=ZJY w t-(∫ s in 0..t.val,JC s (m w (projIcc 0 T hT s))))
    (hmI : ∀ᵐ w ∂P,∀ t,m w t=m0+(∫ s in 0..t.val,A s (m w (projIcc 0 T hT s)))+ZKDI w t)
    (hY : ∀ᵐ w ∂P,∀ t,Y w t=(∫ s in 0..t.val,C s (m w (projIcc 0 T hT s)))+ZDI w t) :
    Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap Y inferInstance)] m ∧
    nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)=
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap I inferInstance) := by
  let GY := nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)
  let GI := nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap I inferInstance)
  letI : MeasurableSpace Ω := mΩ
  have hGY : GY≤mΩ := null_augmented_le (m := mΩ) P _ hYm.comap_le
  have hGI : GI≤mΩ := null_augmented_le (m := mΩ) P _ hIm.comap_le
  have hnY Q (hm : MeasurableSet[mΩ] Q) (hq : P Q=0) : MeasurableSet[GY] Q :=
    MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hm,hq⟩)
  have hnI Q (hm : MeasurableSet[mΩ] Q) (hq : P Q=0) : MeasurableSet[GI] Q :=
    MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hm,hq⟩)
  have hmGY : Measurable[GY] m :=
    linear_reconstruction_ae_measurable (m := mΩ) P GY hGY hnY F hF T hT (fun _ => m0) measurable_const ZKY m hKY hmm hmY
  have hmGI : Measurable[GI] m :=
    linear_reconstruction_ae_measurable (m := mΩ) P GI hGI hnI A hA T hT (fun _ => m0) measurable_const ZKDI m hKDI hmm hmI
  letI : MeasurableSpace Ω := mΩ
  refine ⟨hmGY,?_⟩
  apply completed_information_eq_of_mutual_measurability (m := mΩ) P Y I
  · letI : MeasurableSpace Ω := GI
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have he : (fun w => Y w t)=ᵐ[P] (fun w => (∫ s in 0..t.val,C s (m w (projIcc 0 T hT s)))+ZDI w t) :=
      hY.mono (fun w hw => hw t)
    exact Asakura.FullAudit.measurable_of_augmented_ae P hGI hnI _ _
      ((continuous_eval_const t).measurable.comp hYm)
      ((drift_history_measurable GI T hT C hC m hmGI t).add
        ((continuous_eval_const t).measurable.comp hDI)) he
  · letI : MeasurableSpace Ω := GY
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have he : (fun w => I w t)=ᵐ[P] (fun w => ZJY w t-(∫ s in 0..t.val,JC s (m w (projIcc 0 T hT s)))) :=
      hI.mono (fun w hw => hw t)
    exact Asakura.FullAudit.measurable_of_augmented_ae P hGY hnY _ _
      ((continuous_eval_const t).measurable.comp hIm)
      (((continuous_eval_const t).measurable.comp hJY).sub
        (drift_history_measurable GY T hT JC hJC m hmGY t)) he

end Asakura.Chapter10
