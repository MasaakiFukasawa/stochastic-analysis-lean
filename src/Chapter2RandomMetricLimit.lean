import Chapter2RandomMetricCompletion

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem truncated_distance_triangle {E : Type*} [MetricSpace E] (x y z : E) :
    min 1 (dist x z) ≤ min 1 (dist x y)+min 1 (dist y z) := by
  have htri := dist_triangle x y z
  have h0 : 0 ≤ min 1 (dist x z) := le_min zero_le_one dist_nonneg
  have h1 : min 1 (dist x z) ≤ 1 := min_le_left _ _
  have hd : min 1 (dist x z) ≤ dist x z := min_le_right _ _
  by_cases hxy : dist x y ≤ 1
  · rw [min_eq_right hxy]
    by_cases hyz : dist y z ≤ 1
    · rw [min_eq_right hyz]; linarith
    · rw [min_eq_left (not_le.1 hyz).le]; linarith [dist_nonneg (x := x) (y := y)]
  · rw [min_eq_left (not_le.1 hxy).le]
    have h : 0 ≤ min 1 (dist y z) := le_min zero_le_one dist_nonneg
    linarith

theorem integrable_truncated_distance
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => min 1 (dist (X ω) (Y ω))) P := by
  apply Integrable.of_bound (measurable_const.min (hX.dist hY)).aestronglyMeasurable 1
  exact .of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_min zero_le_one dist_nonneg)]
    exact min_le_left _ _

/-- Bounded dominated convergence takes pathwise subsequence convergence
back to the expectation metric. -/
theorem truncated_metric_ae_limit
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ℕ → Ω → E) (Y : Ω → E) (hm : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ∫ ω, min 1 (dist (X n ω) (Y ω)) ∂P) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun n => (measurable_const.min ((hm n).dist hY)).aestronglyMeasurable)
    (integrable_const (1:ℝ))
    (fun n => .of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min zero_le_one dist_nonneg)]
      exact min_le_left _ _) (f := fun _ : Ω => (0:ℝ)) (by
        filter_upwards [hlim] with ω hω
        have hd : Tendsto (fun n => dist (X n ω) (Y ω)) atTop (𝓝 0) := by
          simpa using hω.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => Y ω) atTop (𝓝 (Y ω)))
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).min hd)
  simpa using h

/-- Completeness for random variables valued in a complete separable
metric space, with the manuscript's subsequence, Borel-Cantelli and DCT proof. -/
theorem truncated_metric_cauchy_limit
    {Ω E : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Nonempty E] (X : ℕ → Ω → E) (hm : ∀ n, Measurable (X n))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (∫ ω, min 1 (dist (X n ω) (X m ω)) ∂P) < ε) :
    ∃ Y : Ω → E, Measurable Y ∧
      Tendsto (fun n => ∫ ω, min 1 (dist (X n ω) (Y ω)) ∂P) atTop (𝓝 0) := by
  obtain ⟨k,hk,hklim⟩ := truncated_metric_cauchy_subsequence P X hm hc
  obtain ⟨N,Y,hN,hNP,hY,hall⟩ := measurable_limit_after_null_modification P (Classical.choice ‹Nonempty E›)
    (fun n => X (k n)) (fun n => hm _) hklim
  have hsub : ∀ᵐ ω ∂P, Tendsto (fun n => X (k n) ω) atTop (𝓝 (Y ω)) := by
    have hn : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]
      simpa using hNP
    filter_upwards [hn] with ω hω
    simpa only [if_neg hω] using hall ω
  have hs := truncated_metric_ae_limit P (fun n => X (k n)) Y (fun n => hm _) hY hsub
  refine ⟨Y,hY,Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨n0,hn0⟩ := hc (ε/2) (by linarith)
  obtain ⟨j0,hj0⟩ := Metric.tendsto_atTop.1 hs (ε/2) (by linarith)
  let j := max n0 j0
  have hjn : n0 ≤ k j := (le_max_left _ _).trans (hk.id_le j)
  have hjj : j0 ≤ j := le_max_right _ _
  refine ⟨n0,fun n hn => ?_⟩
  have hb := hj0 j hjj
  have hb0 : 0 ≤ ∫ ω, min 1 (dist (X (k j) ω) (Y ω)) ∂P := integral_nonneg fun ω => le_min zero_le_one dist_nonneg
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg hb0] at hb
  have htri : (∫ ω, min 1 (dist (X n ω) (Y ω)) ∂P) ≤
      (∫ ω, min 1 (dist (X n ω) (X (k j) ω)) ∂P) +
      (∫ ω, min 1 (dist (X (k j) ω) (Y ω)) ∂P) := by
    rw [← integral_add (integrable_truncated_distance P _ _ (hm n) (hm _))
      (integrable_truncated_distance P _ _ (hm _) hY)]
    apply integral_mono (integrable_truncated_distance P _ _ (hm n) hY)
      ((integrable_truncated_distance P _ _ (hm n) (hm _)).add (integrable_truncated_distance P _ _ (hm _) hY))
    exact fun ω => truncated_distance_triangle _ _ _
  have hn0' := hn0 n hn (k j) hjn
  have hpos : 0 ≤ ∫ ω, min 1 (dist (X n ω) (Y ω)) ∂P := integral_nonneg fun ω => le_min zero_le_one dist_nonneg
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hpos]
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.truncated_distance_triangle
#print axioms Asakura.Chapter2Complete.integrable_truncated_distance
#print axioms Asakura.Chapter2Complete.truncated_metric_ae_limit
#print axioms Asakura.Chapter2Complete.truncated_metric_cauchy_limit
