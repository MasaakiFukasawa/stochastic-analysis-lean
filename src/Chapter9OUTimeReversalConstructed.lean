import Chapter9OUTimeReversal
import Chapter9OURandomInitial

open MeasureTheory Matrix Set
open scoped ContDiff
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- End-to-end construction from the given Brownian driver and arbitrary
 measurable initial value, with one common event for the forward equation,
 and the fully verified reverse Brownian motion, drift and densities. -/
theorem standard_ou_time_reversal_constructed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (ξ : Ω → Fin d → ℝ) (hξ : Measurable[B.F ⊥] ξ) (T : ℝ) (hT : 0<T) :
    ∃ N : Fin d → Fin d → HalfClosedTime → Ω → ℝ,
      (∀ i j,LocalMProcessWitness P B.F (N i j)) ∧
      (∀ i j,ItoCovarianceFormula P B.F (B.W j)
        (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j)) ∧
      let X := fun r w i => Real.exp (-r)*(ξ w i+∑ j,N i j (realTimeClamp r) w)
      let μ := P.map (X 0)
      (∀ᵐ w ∂P,∀ r,0≤r → ∀ i,X r w i=ξ w i-(∫ s in 0..r,X s w i)+Real.sqrt 2*B.W i (realTimeClamp r) w) ∧
      BrownianBefore P (reversedNaturalInformation P X T) (reverseBrownian μ X T) T ∧
      (∀ s,0≤s → s<T → ∀ w i,
        IntervalIntegrable (fun r => ouReverseDrift μ (T-r,X (T-r) w) i) volume 0 s ∧
        X (T-s) w i=X T w i+(∫ r in 0..s,ouReverseDrift μ (T-r,X (T-r) w) i)+
          Real.sqrt 2*reverseBrownian μ X T s w i) ∧
      (∀ s,0≤s → s<T → P.map (X (T-s))=
        volume.withDensity (fun y => ENNReal.ofReal (ouCoordinateDensity μ (T-s,y)))) := by
  obtain ⟨N,hN,hNI,hforward⟩ := standard_ou_common_initial_construction P B
  refine ⟨N,hN,hNI,?_,standard_ou_time_reversal P B N hN hNI ξ hξ T hT⟩
  filter_upwards [hforward] with w hw
  exact hw (ξ w)
end Asakura.Chapter9
