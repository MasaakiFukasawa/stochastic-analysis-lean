import FullAuditStrongMarkovWritten
import Chapter7BrownianSmallTime
import Chapter7IntervalEventMeasurable

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2400000

/-- Strong Markov plus the proved maximal inequality gives the conditional
failure estimate in its test-event form; it is not assumed as an extra
probabilistic hypothesis. -/
theorem strong_markov_stay_failure
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (τ : Ω → ℝ≥0)
    (hτ : ∀ t,MeasurableSet[Asakura.nullAugmentation P (pastSigma B t)] {w | τ w ≤ t})
    (δ : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[writtenStoppedSpace m (fun t => Asakura.nullAugmentation P (pastSigma B t)) τ hτ] E) :
    P (E ∩ {w | ¬∀ t : ℝ≥0,t ≤ δ → |B (τ w+t) w-B (τ w) w| ≤ 1}) ≤
      ENNReal.ofReal (δ:ℝ)*P E := by
  let X := fun t w => B (τ w+t) w-B (τ w) w
  obtain ⟨hX,hXc,hI⟩ := brownian_strong_markov_written P B hB hm hc τ hτ
  let H := MeasurableSpace.comap (fun w t => X t w) inferInstance
  have hXmH t : Measurable[H] (X t) := (measurable_pi_apply t).comp
    (show Measurable[H] (fun w t => X t w) from Measurable.of_comap_le le_rfl)
  have hXm t : Measurable[m] (X t) := by
    let J : Finset ℝ≥0 := {t}
    exact stopping_future_test_measurable (m := m) B hm hc
      (fun t => Asakura.nullAugmentation (m := m) P (pastSigma B t)) (fun _ _ he => he.1) τ hτ J
      (fun z => z ⟨t,Finset.mem_singleton_self t⟩) (continuous_apply _)
  let A := {w | ∀ t : ℝ≥0,t ≤ δ → |X t w| ≤ 1}
  have hA : MeasurableSet[H] A := interval_stay_measurable H X hXc δ (fun t _ => hXmH t)
  have hprob : P Aᶜ ≤ ENNReal.ofReal (δ:ℝ) := by
    have h := ENNReal.ofReal_le_ofReal (brownian_small_time_failure P X hX hXm hXc δ)
    rw [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    convert h using 1
    congr 1
    ext w
    simp [A]
  have heq := (hI.indepSet_of_measurableSet hA.compl hE).measure_inter_eq_mul
  change P (E ∩ Aᶜ) ≤ ENNReal.ofReal (δ:ℝ)*P E
  rw [inter_comm,heq]
  exact mul_le_mul' hprob le_rfl

end Asakura.Chapter7
