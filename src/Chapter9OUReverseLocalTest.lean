import Chapter9ReverseLocalTest
import Chapter9OUReverseTest
open MeasureTheory Matrix Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem standard_ou_reverse_local_test {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (T b : ℝ) (hb : 0≤b) (hbT : b<T) :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    LocalMProcessWitness P
      (fun (t : HalfClosedTime) => reversedNaturalInformation P X T (finitePrefixTime b hb t).val)
      (fun t w => reverseCompensated (P.map (X 0)) T (fun r => X (T-r)) f
        (finitePrefixTime b hb t).val w) := by
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  have hXm r : Measurable (X r) := (standard_ou_adapted P B N hN ξ hξ r).mono (B.le _) le_rfl
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).mpr inferInstance
  apply ou_reverse_local_smooth_test P (P.map (X 0)) X hXm
    (standard_ou_path P B N hN ξ) T _ f hf b hb hbT
  intro a c ha hac hcT g hg
  have he := standard_ou_reverse_kernel_conditional P B N hN hNI ξ hξ
    (T-c) (T-a) T (by linarith) (by linarith) (by linarith) g hg
  have hh : T-a-(T-c)=c-a := by ring
  simpa only [reversedNaturalInformation,ouReverseParamTransition,ouCoordinateDensity,hh,X] using! he
end Asakura.Chapter9
