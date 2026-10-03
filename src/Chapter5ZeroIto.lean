import Chapter5ClockSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The stochastic integral against the zero martingale vanishes, derived
from the covariance characterization and the separation proposition. -/
theorem integral_against_zero_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Y : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hY : LocalMProcessWitness P F Y)
    (hI : ItoCovarianceFormula P F (fun _ _ => 0) H Y) :
    ∀ᵐ w ∂P, ∀ t, t < ⊤ → Y t w = 0 := by
  apply local_covariance_separates P F hF hle Y (fun _ _ => 0) hY (zero_local_process P hT F)
  intro N hN
  obtain ⟨A,hA⟩ := local_covariance_witness_exists P F hF hle hnull N N hN hN
  have hzero : LocalCovarianceWitness P F (fun _ _ => 0) N (fun _ _ => 0) := by
    refine ⟨?_,?_⟩
    · simpa only [zero_mul,sub_zero] using zero_local_process P hT F
    · simpa only [zero_mul] using hA.variation.smul F 0
  obtain ⟨D,hD,hID⟩ := hI N (fun _ _ => 0) hN hzero
  refine ⟨D,(fun _ _ => 0),hD,hzero,?_⟩
  apply local_covariance_common_time_equality P hT F Y N D (fun _ _ => 0) hY hN hD
    (fun _ => continuous_const)
  intro t ht
  obtain ⟨d,hd,hdT,rfl⟩ := finite_closed_time_real t ht
  obtain ⟨ν,hν,hν0,_,he⟩ := hID d hd hdT
  filter_upwards [hν0,he] with w hw hew
  have hz : ν w = 0 := by
    apply signed_measure_ext_positive_Ioc _ _ hw
    · simp [SignedMeasure.totalVariation_zero]
    · intro a b ha hab
      simpa using hν w a b ha hab
  rw [hew,hz]
  simp [signedIntegralRaw,SignedMeasure.toJordanDecomposition_zero]

end Asakura.Chapter5
