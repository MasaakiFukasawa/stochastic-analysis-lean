import Chapter9BrownianBefore
import Chapter9OUReverseTest
import Chapter9ReverseLogScore
open MeasureTheory Matrix Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Complete finite-horizon time reversal for the actual Ito-constructed
 OU process: Brownian driver, integrable displayed drift, integral SDE,
 and all reversed marginal densities. No reverse-process martingale,
 bracket, transition, or differentiability hypothesis is assumed. -/
theorem standard_ou_time_reversal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (T : ℝ) (hT : 0<T) :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    let μ := P.map (X 0)
    BrownianBefore P (reversedNaturalInformation P X T) (reverseBrownian μ X T) T ∧
      (∀ s,0≤s → s<T → ∀ w i,
        IntervalIntegrable (fun r => ouReverseDrift μ (T-r,X (T-r) w) i) volume 0 s ∧
        X (T-s) w i=X T w i+(∫ r in 0..s,ouReverseDrift μ (T-r,X (T-r) w) i)+
          Real.sqrt 2*reverseBrownian μ X T s w i) ∧
      (∀ s,0≤s → s<T → P.map (X (T-s))=
        volume.withDensity (fun y => ENNReal.ofReal (ouCoordinateDensity μ (T-s,y)))) := by
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  let μ := P.map (X 0)
  have hXm r : Measurable (X r) := (standard_ou_adapted P B N hN ξ hξ r).mono (B.le _) le_rfl
  haveI : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).mpr inferInstance
  have hXc := standard_ou_path P B N hN ξ
  refine ⟨reverse_brownian_is_brownian P μ X hXm hXc T ?_,?_,?_⟩
  · intro a c ha hac hcT g hg
    have he := standard_ou_reverse_kernel_conditional P B N hN hNI ξ hξ
      (T-c) (T-a) T (by linarith) (by linarith) (by linarith) g hg
    have hh : T-a-(T-c)=c-a := by ring
    simpa only [reversedNaturalInformation,ouReverseParamTransition,ouCoordinateDensity,hh,X,μ] using! he
  · intro s hs hsT w i
    exact ⟨(reverse_drift_path_continuous μ X hXc T s hsT w i).intervalIntegrable_of_Icc hs,
      reverse_brownian_sde_identity μ X T s w i⟩
  · intro s hs hsT
    simpa only [sub_zero,ouCoordinateDensity,gaussianKernel,ouExponent,X,μ] using!
      standard_ou_marginal_from_time P B N hN hNI ξ hξ 0 (T-s) le_rfl (sub_pos.mpr hsT)
end Asakura.Chapter9
