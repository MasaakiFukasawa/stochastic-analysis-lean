import Chapter2CanonicalCovarianceData
import Chapter2RegularCovarianceChoice
import Chapter2CovarianceAbsoluteContinuity
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The actual covariance has a finite signed Stieltjes measure supported
on the finite prefix. Regular quadratic variations are constructed, not
assumed as additional hypotheses on the manuscript's covariance. -/
theorem supported_covariance_measure
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∃ ν : Ω → SignedMeasure ℝ,
      (∀ ω a b, 0 ≤ a → a ≤ b → ν ω (Ioc a b) =
        C (min (realTimeClamp b) (realTimeClamp d)) ω-C (min (realTimeClamp a) (realTimeClamp d)) ω) ∧
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(ν ω).totalVariation, r ∈ Ioc 0 d) := by
  obtain ⟨A,hA,hAm,hAc,_⟩ := local_quadratic_variation_regular_choice P F hF hle hnull X hX
  obtain ⟨B,hB,hBm,hBc,_⟩ := local_quadratic_variation_regular_choice P F hF hle hnull Y hY
  obtain ⟨hAdm,hAdc⟩ := regular_covariance_on_real_intervals A hAm hAc d hd hdT
  obtain ⟨hBdm,hBdc⟩ := regular_covariance_on_real_intervals B hBm hBc d hd hdT
  obtain ⟨ν,hcs,hν,_⟩ := canonical_covariance_measure_data P F hF hle hnull X Y A B C
    hX hY hA hB hC d hd hdT hAdm hBdm hAdc hBdc
  refine ⟨ν,hν,?_⟩
  filter_upwards [hcs] with ω hcsω
  let α := (intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
    (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure
  let β := (intervalStieltjes 0 d hd (fun r => B (realTimeClamp r) ω) (hBdm ω)
    (fun r hr => (hBdc ω r hr).mono inter_subset_left)).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite _ _ _ _ _ _
  letI : IsFiniteMeasure β := intervalStieltjes_finite _ _ _ _ _ _
  have hac : (ν ω).totalVariation ≪ α := signed_cs_absolute_continuity α β (ν ω) hcsω
  exact (Measure.ae_le_iff_absolutelyContinuous.mpr hac) (interval_stieltjes_ae_mem_Ioc 0 d hd _ (hAdm ω)
    (fun r hr => (hAdc ω r hr).mono inter_subset_left))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.supported_covariance_measure
