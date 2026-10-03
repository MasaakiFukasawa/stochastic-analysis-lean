import Chapter4PicardPaths
import Chapter2RandomMetricCompletion
import FullAuditPathSpaceExercise

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

/-- The absolute uniform Picard limit can be chosen continuously and adapted
on one common null set. No adaptedness of the limit is assumed. -/
theorem adapted_picard_series_limit
    {Ω D : Type*} {m : MeasurableSpace Ω}
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : D → MeasurableSpace Ω)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z : ℕ → Ω → C(D,ℝ)) (hZ : ∀ n, Measurable[m] (Z n))
    (ha : ∀ n t, Measurable[F t] (fun ω => Z n ω t))
    (A a : ℝ) (ha0 : 0 ≤ a)
    (hb : ∀ n, eLpNorm (Z n) 2 P ≤ ENNReal.ofReal (A*Real.sqrt (a^n/(n.factorial:ℝ)))) :
    ∃ Y : Ω → C(D,ℝ), Measurable[m] Y ∧
      (∀ t, Measurable[F t] (fun ω => Y ω t)) ∧
      ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range n, Z k ω) atTop (𝓝 (Y ω)) := by
  classical
  let S := fun n ω => ∑ k ∈ Finset.range n, Z k ω
  have hS n : Measurable[m] (S n) := Finset.measurable_sum _ (fun k _ => hZ k)
  have hlim : ∀ᵐ ω ∂P, ∃ y, Tendsto (fun n => S n ω) atTop (𝓝 y) := by
    filter_upwards [picard_path_series P Z (fun n => (hZ n).aestronglyMeasurable) A a ha0 hb] with ω hω
    exact ⟨∑' n, Z n ω,hω.2.hasSum.tendsto_sum_nat⟩
  obtain ⟨N,Y,hN,hNP,hY,hall⟩ :=
    Asakura.Chapter2Complete.measurable_limit_after_null_modification P 0 S hS hlim
  refine ⟨Y,hY,?_,?_⟩
  · intro t
    letI : MeasurableSpace Ω := F t
    have hSm n : Measurable (fun ω => if ω ∈ N then (0:ℝ) else S n ω t) := by
      apply Measurable.ite (hnull t N hN hNP) measurable_const
      simpa only [S,ContinuousMap.sum_apply] using
        (Finset.measurable_sum (Finset.range n) (fun k _ => ha k t))
    apply measurable_of_tendsto_metrizable hSm
    apply tendsto_pi_nhds.mpr
    intro ω
    have hh := (continuous_eval_const t : Continuous (fun f : C(D,ℝ) => f t)).continuousAt.tendsto.comp (hall ω)
    by_cases hω : ω ∈ N
    · simpa [Function.comp_def,hω] using hh
    · simpa [Function.comp_def,hω] using hh
  · have hn : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hNP
    filter_upwards [hn] with ω hω
    simpa only [if_neg hω,S] using hall ω

end Asakura.Chapter4
