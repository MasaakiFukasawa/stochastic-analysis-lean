import Chapter2PathMetric

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

theorem integrable_path_distance
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : Ω → C(D,ℝ)) (hX : Measurable X) (hY : Measurable Y) :
    Integrable (fun ω => pathDistance K (X ω) (Y ω)) P := by
  apply Integrable.of_bound (path_distance_measurable K X Y hX hY).aestronglyMeasurable 1
  exact .of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (path_distance_bounds K _ _).1]
    exact (path_distance_bounds K _ _).2

/-- The printed weighted path distance controls the probability of a
large error on any fixed compact interval. -/
theorem path_distance_stage_probability
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : Ω → C(D,ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (j : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    P {ω | ε < compactStageDist K j (X ω) (Y ω)} ≤
      ENNReal.ofReal ((∫ ω, pathDistance K (X ω) (Y ω) ∂P) / ((1/2:ℝ)^(j+1)*ε)) := by
  let w := (1/2:ℝ)^(j+1)
  have hw : 0 < w := pow_pos (by norm_num) _
  have hmeas := path_distance_measurable K X Y hX hY
  have hi := integrable_path_distance P K X Y hX hY
  have hmark := meas_ge_le_lintegral_div (μ := P) hmeas.ennreal_ofReal.aemeasurable
    (ENNReal.ofReal_ne_zero_iff.2 (mul_pos hw hε)) ENNReal.ofReal_ne_top
  have hinc : {ω | ε < compactStageDist K j (X ω) (Y ω)} ⊆
      {ω | ENNReal.ofReal (w*ε) ≤ ENNReal.ofReal (pathDistance K (X ω) (Y ω))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (le_min hε1 hω.le) hw.le).trans
      (path_distance_controls_stage K (X ω) (Y ω) j))
  apply (measure_mono hinc).trans
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun ω => (path_distance_bounds K _ _).1),
    ← ENNReal.ofReal_div_of_pos (mul_pos hw hε)] at hmark
  exact hmark

/-- The Cauchy condition for the expectation of the manuscript's path
distance produces a subsequence converging locally uniformly almost surely. -/
theorem path_metric_cauchy_subsequence
    {Ω D : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X : ℕ → Ω → C(D,ℝ)) (hm : ∀ n, Measurable (X n))
    (hc : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
      (∫ ω, pathDistance K (X n ω) (X m ω) ∂P) < ε) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ ω ∂P, ∃ y : C(D,ℝ),
      Tendsto (fun n => X (k n) ω) atTop (𝓝 y) := by
  let d := fun n => (1/2:ℝ)^n
  let w := fun n => (1/2:ℝ)^(n+1)
  have hd : Summable d := summable_geometric_of_abs_lt_one (by norm_num)
  have hdpos (n) : 0 < d n := pow_pos (by norm_num) n
  have hwpos (n) : 0 < w n := pow_pos (by norm_num) _
  obtain ⟨k,hk,hsmall⟩ := cauchy_choose_rapid_subsequence
    (fun n m => ∫ ω, pathDistance K (X n ω) (X m ω) ∂P) hc
    (fun n => w n * (d n)^2) (fun n => mul_pos (hwpos n) (sq_pos_of_pos (hdpos n)))
  refine ⟨k,hk,?_⟩
  have hb (n) : P {ω | d n < compactStageDist K n (X (k n) ω) (X (k (n+1)) ω)} ≤ ENNReal.ofReal (d n) := by
    apply (path_distance_stage_probability P K (X (k n)) (X (k (n+1))) (hm _) (hm _) n (d n)
      (hdpos n) (pow_le_one₀ (by norm_num) (by norm_num))).trans
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_div_of_nonneg_right (hsmall n).le (mul_pos (hwpos n) (hdpos n)).le).trans_eq
    change w n * (d n)^2 / (w n * d n) = d n
    field_simp [(hwpos n).ne', (hdpos n).ne']
  have hs : (∑' n, P {ω | d n < compactStageDist K n (X (k n) ω) (X (k (n+1)) ω)}) < ∞ := by
    apply (ENNReal.tsum_le_tsum hb).trans_lt
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hdpos n).le) hd]
    exact ENNReal.ofReal_lt_top
  exact diagonal_compact_increment_limit P K (fun n => X (k n)) d hd
    (fun n => measurableSet_lt measurable_const (compact_stage_distance_measurable K _ _ (hm _) (hm _) n)) hs

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integrable_path_distance
#print axioms Asakura.Chapter2Complete.path_distance_stage_probability
#print axioms Asakura.Chapter2Complete.path_metric_cauchy_subsequence
