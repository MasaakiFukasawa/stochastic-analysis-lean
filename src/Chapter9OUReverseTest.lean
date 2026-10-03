import Chapter9ReverseTestIncrement
import Chapter9OUReverseKernel

open MeasureTheory Matrix Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Actual OU paths are continuous even before any reverse filtration is
 introduced; the same stochastic-integral representatives are used throughout. -/
theorem standard_ou_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (ξ : Ω → Fin d → ℝ) (w : Ω) :
    Continuous (fun r i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)) := by
  apply continuous_pi
  intro i
  apply Continuous.mul (by fun_prop)
  apply continuous_const.add
  apply continuous_finsetSum
  intro j _
  apply continuous_iff_continuousAt.mpr
  intro r
  exact ((hN i j).path P B.F w _ (half_real_time_finite r)).comp real_time_clamp_continuous.continuousAt

/-- The compact-test compensated increment identity for the actual process,
 derived from the forward Ito construction and actual Gaussian densities. -/
theorem standard_ou_reverse_test_increment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (T s t : ℝ) (hs : 0≤s) (hst : s<t) (htT : t<T) :
    let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
    P[(fun w => f (X (T-t) w)-
      ∫ h,ouReverseGenerator (P.map (X 0)) f (T-(s+h),X (T-(s+h)) w)
        ∂volume.restrict (Ioc 0 (t-s)))|reversedNaturalInformation P X T s]=ᵐ[P]
      (fun w => f (X (T-s) w)) := by
  let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
  have hXm r : Measurable (X r) := (standard_ou_adapted P B N hN ξ hξ r).mono (B.le _) le_rfl
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).mpr inferInstance
  apply ou_reverse_test_increment P (P.map (X 0)) X hXm
    (measurable_uncurry_of_continuous_of_measurable (standard_ou_path P B N hN ξ) hXm)
    T _ f hf hfc s t hs hst htT
  intro a b ha hab hbT g hg
  have he := standard_ou_reverse_kernel_conditional P B N hN hNI ξ hξ
    (T-b) (T-a) T (by linarith) (by linarith) (by linarith) g hg
  have hh : T-a-(T-b)=b-a := by ring
  simpa only [reversedNaturalInformation,ouReverseParamTransition,ouCoordinateDensity,hh,X] using! he
end Asakura.Chapter9
