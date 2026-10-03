import Chapter2ItoCovarianceCharacterization
import Chapter2SignedRestriction
import Chapter2RightContinuousCommonEquality
import Chapter2RightContinuousCumulative

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The covariance characterization yields a single actual signed-measure
cumulative integral on each finite horizon, simultaneously at every time.
The measures at shorter horizons are identified by restriction, and right
continuity removes the uncountable family of exceptional null sets. -/
theorem ItoCovarianceFormula.finite_process_formula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (hY : LocalMProcessWitness P F Y) (hH : ∀ ω, Measurable (fun r => H (ω,r)))
    (hIto : ItoCovarianceFormula P F X H Y)
    (Y0 C0 : ClosedTime T → Ω → ℝ) (hY0 : LocalMProcessWitness P F Y0)
    (hC0 : LocalCovarianceWitness P F X Y0 C0) :
    ∃ D, LocalCovarianceWitness P F Y Y0 D ∧
      ∀ b : ℝ, 0 ≤ b → (b:EReal) < T → ∃ ν : Ω → SignedMeasure ℝ,
        (∀ ω s t, 0 ≤ s → s ≤ t → ν ω (Ioc s t) =
          C0 (min (realTimeClamp t) (realTimeClamp b)) ω -
          C0 (min (realTimeClamp s) (realTimeClamp b)) ω) ∧
        (∀ᵐ ω ∂P, (ν ω).totalVariation (Iic 0) = 0) ∧
        (∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (ν ω).totalVariation) ∧
        (∀ᵐ ω ∂P, ∀ d ∈ Icc 0 b,
          D (realTimeClamp d) ω = signedCumulative (ν ω) (fun r => H (ω,r)) d) := by
  obtain ⟨D,hD,hd⟩ := hIto Y0 C0 hY0 hC0
  refine ⟨D,hD,?_⟩
  intro b hb hbT
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hd b hb hbT
  refine ⟨ν,hν,hν0,hνi,?_⟩
  have hfixed d (hdb : d ∈ Icc 0 b) :
      D (realTimeClamp d) =ᵐ[P] fun ω => signedCumulative (ν ω) (fun r => H (ω,r)) d := by
    have hdT : (d:EReal) < T := (EReal.coe_le_coe hdb.2).trans_lt hbT
    obtain ⟨κ,hκ,hκ0,hκi,hκD⟩ := hd d hdb.1 hdT
    filter_upwards [hν0,hνi,hκ0,hκD] with ω hn0 hni hk0 hkD
    have hEq : κ ω = (ν ω).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C0 (realTimeClamp r) ω)
        b d hdb.1 hdb.2 (κ ω) (ν ω) hk0 hn0
      · intro s t hs hst
        simpa only [real_time_clamp_mono.map_min] using hκ ω s t hs hst
      · intro s t hs hst
        simpa only [real_time_clamp_mono.map_min] using hν ω s t hs hst
    rw [hkD,hEq,signed_integral_restrict (ν ω) measurableSet_Iic _ (hH ω) hni.integrableOn]
    rfl
  apply right_continuous_common_equality P b hb
    (fun d => D (realTimeClamp d))
    (fun d ω => signedCumulative (ν ω) (fun r => H (ω,r)) d) _ _ hfixed
  · exact ae_of_all _ (fun ω d hd0 hdb => by
      have hdt : realTimeClamp (T := T) d < ⊤ := by
        change (realTimeClamp d:EReal) < T
        rw [real_time_clamp_eq d hd0 ((EReal.coe_le_coe hdb.le).trans hbT.le)]
        exact (EReal.coe_le_coe hdb.le).trans_lt hbT
      have hcont := ((hY.path P F ω _ hdt).mul (hY0.path P F ω _ hdt)).sub
        (hD.defect.path P F ω _ hdt)
      have hc : ContinuousAt (fun s => D s ω) (realTimeClamp d) := by
        convert hcont using 1
        funext s
        dsimp only [Pi.sub_apply,Pi.mul_apply]
        ring
      exact (hc.comp real_time_clamp_continuous.continuousAt).continuousWithinAt)
  · exact hνi.mono (fun ω hi d _ _ => signed_cumulative_right_continuous (ν ω) _ hi d)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ItoCovarianceFormula.finite_process_formula
