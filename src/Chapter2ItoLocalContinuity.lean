import Chapter2ItoCharacterizedEnergy
import Chapter2LenglartConvergence
import Chapter2PathProbabilityMetric
import Chapter2QuadraticCauchyLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Continuity at zero of the full integral, for the actual local
probability topology on integrands and the manuscript's path-distance metric.
Energy of the output is proved from the elementary construction. -/
theorem ito_integral_continuous_at_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hA : LocalCovarianceWitness P F X X A)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (H : ℕ → Ω × ℝ → ℝ)
    (hH : ∀ k n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => H k (z.1,z.2.val)))
    (hi : ∀ k n, ∀ᵐ ω ∂P, Integrable (fun r => H k (ω,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) ω) (hAm n ω)
        (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure)
    (Y : ℕ → Ω → C(Iio (⊤ : ClosedTime T),ℝ))
    (hY : ∀ k, LocalMProcessWitness P F (fun t ω => extendOpenPath (Y k ω) t))
    (hYI : ∀ k, ItoCovarianceFormula P F X (H k) (fun t ω => extendOpenPath (Y k ω) t))
    (hp : ∀ j δ, 0 < δ → Tendsto (fun k => P {ω | δ ≤ ∫ r, H k (ω,r)^2
      ∂(intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure}) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, pathDistance
      (intervalTimeExhaustion (fun n => realTimeClamp (c n)) hct hcut hcc) (Y k ω) 0 ∂P) atTop (𝓝 0) := by
  letI : LocallyCompactSpace (Iio (⊤ : ClosedTime T)) := isOpen_Iio.locallyCompactSpace
  choose B hB heB using fun k => ito_covariance_formula_energy P hT F hF hle hnull X A hX hA
    c hc hcm hcT hct hcut hcc hAm hAc (H k) (hH k) (hi k) _ (hY k) (hYI k)
  have hprob j δ (hδ : 0 < δ) : Tendsto (fun k => P {ω | δ ≤ B k (realTimeClamp (c j)) ω}) atTop (𝓝 0) := by
    have heq k : P {ω | δ ≤ B k (realTimeClamp (c j)) ω} = P {ω | δ ≤ ∫ r, H k (ω,r)^2
      ∂(intervalStieltjes 0 (c j) (hc j).le (fun r => A (realTimeClamp r) ω) (hAm j ω)
        (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure} :=
      measure_congr ((heB k j).mono fun ω hω => by simp only [mem_setOf_eq,hω])
    simpa only [heq] using hp j δ hδ
  apply path_metric_limit_of_probability P _ Y (fun _ _ => 0)
    (fun k => local_martingale_path_measurable P F hle (Y k) (hY k)) (fun _ => measurable_const)
  intro j ε hε
  have hs (t : ClosedTime T) : MeasurableSet[F t] {ω : Ω | realTimeClamp (T := T) (c j) ≤ t} := by
    by_cases ht : realTimeClamp (T := T) (c j) ≤ t <;> simp [ht]
  have hh := local_martingale_probability_of_quadratic_variation P F hF hle hnull
    (fun k t ω => extendOpenPath (Y k ω) t) B hY hB
    (fun _ => realTimeClamp (c j)) hs (fun _ => hcut j) (hprob j) ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le)
  intro k
  apply measure_mono
  intro ω hω
  have hb := interval_stage_distance_le_stopped_sup (fun n => realTimeClamp (c n)) hct hcut hcc (Y k ω) 0 j
  have hz t : extendOpenPath (0 : C(Iio (⊤ : ClosedTime T),ℝ)) t = 0 := by
    simp [extendOpenPath]
  simpa only [hz,sub_zero,mem_setOf_eq] using hω.trans hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.ito_integral_continuous_at_zero
