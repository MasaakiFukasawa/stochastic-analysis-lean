import Chapter2PathMetricSubsequence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Local uniform convergence makes the actual series distance tend to
zero, using its summable geometric bound. -/
theorem path_distance_of_tendsto
    {D : Type*} [TopologicalSpace D] (K : CompactExhaustion D)
    (X : ℕ → C(D,ℝ)) (Y : C(D,ℝ)) (h : Tendsto X atTop (𝓝 Y)) :
    Tendsto (fun n => pathDistance K (X n) Y) atTop (𝓝 0) := by
  letI (j : ℕ) : CompactSpace (K j) := isCompact_iff_compactSpace.1 (K.isCompact j)
  have hj (j) : Tendsto (fun n => compactStageDist K j (X n) Y) atTop (𝓝 0) := by
    have hr : Tendsto (fun n => (X n).restrict (K j)) atTop (𝓝 (Y.restrict (K j))) :=
      (ContinuousMap.continuous_precomp (⟨Subtype.val,continuous_subtype_val⟩ : C(K j,D))).tendsto _ |>.comp h
    simpa only [dist_self,compactStageDist] using hr.dist (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Y.restrict (K j)) atTop (𝓝 (Y.restrict (K j))))
  have hl (j) : Tendsto (fun n => (1/2:ℝ)^(j+1)*min 1 (compactStageDist K j (X n) Y)) atTop (𝓝 0) := by
    have hmin := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).min (hj j)
    simpa using hmin.const_mul ((1/2:ℝ)^(j+1))
  have hi (n) : Integrable (fun j => (1/2:ℝ)^(j+1)*min 1 (compactStageDist K j (X n) Y)) Measure.count :=
    integrable_count_iff.2 (path_distance_summable K (X n) Y).norm
  have hsum := tendsto_integral_of_dominated_convergence (μ := Measure.count)
    (fun j : ℕ => (1/2:ℝ)^(j+1))
    (fun n => (hi n).aestronglyMeasurable)
    (integrable_count_iff.2 path_weights_summable.norm)
    (fun n => .of_forall fun j => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity)
        (le_min zero_le_one (compact_stage_distance_nonneg K j (X n) Y)))]
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _))
    (f := fun _ : ℕ => (0:ℝ)) (.of_forall hl)
  have he (n) : (∫ j, (1/2:ℝ)^(j+1)*min 1 (compactStageDist K j (X n) Y) ∂Measure.count) = pathDistance K (X n) Y := by
    rw [integral_countable (hi n)]
    simp [Measure.real,Measure.count_singleton, pathDistance]
  simpa only [he,integral_zero] using hsum

theorem path_metric_ae_limit
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X : ℕ → Ω → C(D,ℝ)) (Y : Ω → C(D,ℝ))
    (hm : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ∫ ω, pathDistance K (X n ω) (Y ω) ∂P) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun n => (path_distance_measurable K (X n) Y (hm n) hY).aestronglyMeasurable)
    (integrable_const (1:ℝ))
    (fun n => .of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (path_distance_bounds K _ _).1]
      exact (path_distance_bounds K _ _).2) (f := fun _ : Ω => (0:ℝ))
    (hlim.mono fun ω hω => path_distance_of_tendsto K (fun n => X n ω) (Y ω) hω)
  simpa using h

/-- A Cauchy sequence for the printed expectation metric has a measurable
continuous-path limit; the same subsequence and exceptional set are retained
for the subsequent local-martingale argument. -/
theorem path_metric_cauchy_limit
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X : ℕ → Ω → C(D,ℝ)) (hm : ∀ n, Measurable (X n))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (∫ ω, pathDistance K (X n ω) (X m ω) ∂P) < ε) :
    ∃ (Y : Ω → C(D,ℝ)) (k : ℕ → ℕ) (N : Set Ω),
      Measurable Y ∧ StrictMono k ∧ MeasurableSet N ∧ P N = 0 ∧
      (∀ ω, ω ∉ N → Tendsto (fun n => X (k n) ω) atTop (𝓝 (Y ω))) ∧
      Tendsto (fun n => ∫ ω, pathDistance K (X n ω) (Y ω) ∂P) atTop (𝓝 0) := by
  obtain ⟨k,hk,hklim⟩ := path_metric_cauchy_subsequence P K X hm hc
  have hchoice : ∃ (N : Set Ω) (Y : Ω → C(D,ℝ)), MeasurableSet N ∧ P N = 0 ∧ Measurable Y ∧
      (∀ ω, Tendsto (fun n => if ω ∈ N then 0 else X (k n) ω) atTop (𝓝 (Y ω))) := by
    letI := TopologicalSpace.upgradeIsCompletelyMetrizable C(D,ℝ)
    exact measurable_limit_after_null_modification P 0 (fun n => X (k n)) (fun n => hm _) hklim
  obtain ⟨N,Y,hN,hNP,hY,hall⟩ := hchoice
  have hgood (ω) (hω : ω ∉ N) : Tendsto (fun n => X (k n) ω) atTop (𝓝 (Y ω)) := by
    simpa only [ite_eq_right hω] using hall ω
  have hsub : ∀ᵐ ω ∂P, Tendsto (fun n => X (k n) ω) atTop (𝓝 (Y ω)) := by
    have hn : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hNP
    exact hn.mono hgood
  have hs := path_metric_ae_limit P K (fun n => X (k n)) Y (fun n => hm _) hY hsub
  refine ⟨Y,k,N,hY,hk,hN,hNP,hgood,Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨n0,hn0⟩ := hc (ε/2) (by linarith)
  obtain ⟨j0,hj0⟩ := Metric.tendsto_atTop.1 hs (ε/2) (by linarith)
  let j := max n0 j0
  have hjn : n0 ≤ k j := (le_max_left _ _).trans (hk.id_le j)
  refine ⟨n0,fun n hn => ?_⟩
  have hb := hj0 j (le_max_right _ _)
  have hb0 : 0 ≤ ∫ ω, pathDistance K (X (k j) ω) (Y ω) ∂P :=
    integral_nonneg fun ω => (path_distance_bounds K _ _).1
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg hb0] at hb
  have htri : (∫ ω, pathDistance K (X n ω) (Y ω) ∂P) ≤
      (∫ ω, pathDistance K (X n ω) (X (k j) ω) ∂P) +
      (∫ ω, pathDistance K (X (k j) ω) (Y ω) ∂P) := by
    rw [← integral_add (integrable_path_distance P K _ _ (hm n) (hm _))
      (integrable_path_distance P K _ _ (hm _) hY)]
    apply integral_mono (integrable_path_distance P K _ _ (hm n) hY)
      ((integrable_path_distance P K _ _ (hm n) (hm _)).add (integrable_path_distance P K _ _ (hm _) hY))
    exact fun ω => path_distance_triangle K _ _ _
  have hn0' := hn0 n hn (k j) hjn
  have hpos : 0 ≤ ∫ ω, pathDistance K (X n ω) (Y ω) ∂P := integral_nonneg fun ω => (path_distance_bounds K _ _).1
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hpos]
  linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.path_distance_of_tendsto
#print axioms Asakura.Chapter2Complete.path_metric_ae_limit
#print axioms Asakura.Chapter2Complete.path_metric_cauchy_limit
