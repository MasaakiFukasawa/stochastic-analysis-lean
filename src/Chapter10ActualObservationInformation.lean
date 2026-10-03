import Chapter10ReconstructedInformationAE
import Chapter10MatrixIntegralPath
import Chapter10DriftHistoryMeasurable
import Chapter10ReconstructedInformation
import Chapter10LinearReconstructionAE
import Chapter10CompletedIndependence

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter9 Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter1Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The four reconstruction equations in the filtering proof imply equality
of completed information. The measurability premises here concern only the
deterministic coefficient stochastic integrals, supplied separately by their
actual discrete approximation theorem. -/
theorem actual_integral_observation_information {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Fobs : HalfClosedTime → MeasurableSpace Ω)
    (hFobs : Monotone Fobs) (hle : ∀ t,Fobs t≤mΩ)
    (hnull : ∀ t E,MeasurableSet[mΩ] E → P E=0 → MeasurableSet[Fobs t] E)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    {d r : ℕ} (T : ℝ) (hT : 0≤T)
    (Y I : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (m ZKY ZKDI : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (ZJY ZDI : Ω → C(Icc (0:ℝ) T,Fin r → ℝ))
    (hYm : Measurable[mΩ] Y) (hIm : Measurable[mΩ] I) (hmm : Measurable[mΩ] m)
    (m0 : Fin d → ℝ)
    (F A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (JC C : ℝ → (Fin d → ℝ) →L[ℝ] (Fin r → ℝ))
    (hF : Continuous F) (hA : Continuous A) (hJC : Continuous JC) (hC : Continuous C)
    (K KD : Fin d → Fin r → HalfClosedTime → ℝ)
    (J D : Fin r → Fin r → HalfClosedTime → ℝ)
    (hK : ∀ i j t,t<⊤ → ContinuousAt (K i j) t)
    (hKD : ∀ i j t,t<⊤ → ContinuousAt (KD i j) t)
    (hJ : ∀ i j t,t<⊤ → ContinuousAt (J i j) t)
    (hD : ∀ i j t,t<⊤ → ContinuousAt (D i j) t)
    (hKY : MatrixIntegralPathWitness P Fobs c hc T hT Y K ZKY)
    (hJY : MatrixIntegralPathWitness P Fobs c hc T hT Y J ZJY)
    (hKDI : MatrixIntegralPathWitness P Fobs c hc T hT I KD ZKDI)
    (hDI : MatrixIntegralPathWitness P Fobs c hc T hT I D ZDI)
    (hmY : ∀ᵐ w ∂P,∀ t,m w t=m0+(∫ s in 0..t.val,F s (m w (projIcc 0 T hT s)))+ZKY w t)
    (hI : ∀ᵐ w ∂P,∀ t,I w t=ZJY w t-(∫ s in 0..t.val,JC s (m w (projIcc 0 T hT s))))
    (hmI : ∀ᵐ w ∂P,∀ t,m w t=m0+(∫ s in 0..t.val,A s (m w (projIcc 0 T hT s)))+ZKDI w t)
    (hY : ∀ᵐ w ∂P,∀ t,Y w t=(∫ s in 0..t.val,C s (m w (projIcc 0 T hT s)))+ZDI w t) :
    Measurable[nullAugmentedInformation (m := mΩ) P
      (MeasurableSpace.comap Y inferInstance)] m ∧
    nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap Y inferInstance)=
      nullAugmentedInformation (m := mΩ) P (MeasurableSpace.comap I inferInstance) := by
  exact reconstructed_observation_information_ae P T hT Y I m ZKY ZKDI ZJY ZDI
    hYm hIm hmm m0 F A JC C hF hA hJC hC
    (hKY.measurable_history P Fobs hFobs hle hnull c hc hcT hcc T hT Y hYm K hK ZKY)
    (hJY.measurable_history P Fobs hFobs hle hnull c hc hcT hcc T hT Y hYm J hJ ZJY)
    (hKDI.measurable_history P Fobs hFobs hle hnull c hc hcT hcc T hT I hIm KD hKD ZKDI)
    (hDI.measurable_history P Fobs hFobs hle hnull c hc hcT hcc T hT I hIm D hD ZDI)
    hmY hI hmI hY

end Asakura.Chapter10
