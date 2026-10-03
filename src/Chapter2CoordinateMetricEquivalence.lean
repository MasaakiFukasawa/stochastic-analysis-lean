import Chapter2IntegrandMetricLimit
import Chapter2PathMetricSubsequence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinateMetric {Ω : Type*} (R : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' j : ℕ, (1/2:ℝ)^(j+1)*min 1 (R j ω)

theorem coordinate_metric_bounds {Ω : Type*} (R : ℕ → Ω → ℝ)
    (hn : ∀ j ω, 0 ≤ R j ω) (ω : Ω) :
    0 ≤ coordinateMetric R ω ∧ coordinateMetric R ω ≤ 1 := by
  have hb j : 0 ≤ (1/2:ℝ)^(j+1)*min 1 (R j ω) ∧
      (1/2:ℝ)^(j+1)*min 1 (R j ω) ≤ (1/2:ℝ)^(j+1) := by
    constructor
    · exact mul_nonneg (by positivity) (le_min zero_le_one (hn j ω))
    · exact mul_le_of_le_one_right (by positivity) (min_le_left _ _)
  refine ⟨tsum_nonneg (fun j => (hb j).1),?_⟩
  have h := Summable.tsum_le_tsum (fun j => (hb j).2)
    (Summable.of_nonneg_of_le (fun j => (hb j).1) (fun j => (hb j).2) path_weights_summable) path_weights_summable
  simpa only [coordinateMetric,path_weights_sum] using h

theorem coordinate_metric_measurable {Ω : Type*} [MeasurableSpace Ω]
    (R : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (R j)) :
    Measurable (coordinateMetric R) :=
  Measurable.tsum (fun j => (measurable_const.min (hm j)).const_mul _)

/-- Every positive weighted coordinate is controlled by the printed metric. -/
theorem coordinate_probability_of_metric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → ℕ → Ω → ℝ) (hm : ∀ n j, Measurable (R n j))
    (hn : ∀ n j ω, 0 ≤ R n j ω)
    (hl : Tendsto (fun n => ∫ ω, coordinateMetric (R n) ω ∂P) atTop (𝓝 0)) :
    ∀ j ε, 0 < ε → Tendsto (fun n => P {ω | ε ≤ R n j ω}) atTop (𝓝 0) := by
  intro j ε hε
  let δ := min 1 ε
  have hδ : 0 < δ := lt_min zero_lt_one hε
  let w := (1/2:ℝ)^(j+1)
  have hw : 0 < w := by dsimp [w]; positivity
  have hm' n := coordinate_metric_measurable (R n) (hm n)
  have hb n := coordinate_metric_bounds (R n) (hn n)
  have hi n : Integrable (coordinateMetric (R n)) P := Integrable.of_bound (hm' n).aestronglyMeasurable 1
    (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hb n ω).1]; exact (hb n ω).2))
  have hbound n : P {ω | ε ≤ R n j ω} ≤ ENNReal.ofReal ((∫ ω, coordinateMetric (R n) ω ∂P)/(w*δ)) := by
    have hmark := meas_ge_le_lintegral_div (μ := P) (hm' n).ennreal_ofReal.aemeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hw hδ)) ENNReal.ofReal_ne_top
    have hinc : {ω | ε ≤ R n j ω} ⊆ {ω | ENNReal.ofReal (w*δ) ≤ ENNReal.ofReal (coordinateMetric (R n) ω)} := by
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      have hsum : Summable (fun k : ℕ => (1/2:ℝ)^(k+1)*min 1 (R n k ω)) :=
        Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (le_min zero_le_one (hn n k ω)))
          (fun k => mul_le_of_le_one_right (by positivity) (min_le_left _ _)) path_weights_summable
      calc
        w*δ ≤ w*min 1 (R n j ω) := mul_le_mul_of_nonneg_left (min_le_min_left 1 hω) hw.le
        _ ≤ coordinateMetric (R n) ω := hsum.le_tsum j (fun k _ => mul_nonneg (by positivity) (le_min zero_le_one (hn n k ω)))
    apply (measure_mono hinc).trans
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ (fun ω => (hb n ω).1)),
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hδ)] at hmark
    exact hmark
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hl.div_const (w*δ))
  simp only [zero_div,ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound

/-- Cofinal coordinate families define the same convergence, even when the
horizon sequence is not monotone. This discharges the arbitrary-sequence
point in the manuscript's local metrics. -/
theorem coordinate_metric_cofinal_equivalence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R S : ℕ → ℕ → Ω → ℝ) (hRm : ∀ n j, Measurable (R n j)) (hSm : ∀ n j, Measurable (S n j))
    (hRn : ∀ n j ω, 0 ≤ R n j ω) (hSn : ∀ n j ω, 0 ≤ S n j ω)
    (hRS : ∀ j, ∃ k, ∀ n ω, R n j ω ≤ S n k ω)
    (hSR : ∀ j, ∃ k, ∀ n ω, S n j ω ≤ R n k ω) :
    Tendsto (fun n => ∫ ω, coordinateMetric (R n) ω ∂P) atTop (𝓝 0) ↔
    Tendsto (fun n => ∫ ω, coordinateMetric (S n) ω ∂P) atTop (𝓝 0) := by
  have forward (R S : ℕ → ℕ → Ω → ℝ) (hRm : ∀ n j, Measurable (R n j)) (hSm : ∀ n j, Measurable (S n j))
      (hRn : ∀ n j ω, 0 ≤ R n j ω) (hSn : ∀ n j ω, 0 ≤ S n j ω)
      (hSR : ∀ j, ∃ k, ∀ n ω, S n j ω ≤ R n k ω)
      (hl : Tendsto (fun n => ∫ ω, coordinateMetric (R n) ω ∂P) atTop (𝓝 0)) :
      Tendsto (fun n => ∫ ω, coordinateMetric (S n) ω ∂P) atTop (𝓝 0) := by
    have hprob := coordinate_probability_of_metric P R hRm hRn hl
    have hsp j ε (hε : 0 < ε) : Tendsto (fun n => P {ω | ε ≤ S n j ω}) atTop (𝓝 0) := by
      obtain ⟨k,hk⟩ := hSR j
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hprob k ε hε)
        (fun _ => bot_le) (fun n => measure_mono (fun ω hω => hω.trans (hk n ω)))
    simpa only [coordinateMetric,div_one,Real.rpow_one] using expected_integrand_metric_limit P S hSm hSn 1 zero_lt_one hsp
  exact ⟨forward R S hRm hSm hRn hSn hSR,forward S R hSm hRm hSn hRn hRS⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.coordinate_metric_cofinal_equivalence
