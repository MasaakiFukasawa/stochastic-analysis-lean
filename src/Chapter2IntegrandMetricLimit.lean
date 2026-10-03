import Chapter2BoundedProbabilityMean
import Chapter2PathMetricLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Truncating the pth root of a nonnegative pathwise error gives exactly
the bounded coordinate used in d_A. Probability convergence controls its mean. -/
theorem truncated_root_mean_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (R n)) (hn : ∀ n ω, 0 ≤ R n ω)
    (p : ℝ) (hp : 0 < p)
    (hl : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ R n ω}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, min 1 ((R n ω)^(1/p)) ∂P) atTop (𝓝 0) := by
  apply bounded_error_mean_limit P _
    (fun n => measurable_const.min ((hm n).pow_const (1/p)))
    (fun n ω => ⟨le_min zero_le_one (Real.rpow_nonneg (hn n ω) _),min_le_left _ _⟩)
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hl (ε^p) (Real.rpow_pos_of_pos hε p)) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  have hroot : ε ≤ (R n ω)^(1/p) := hω.trans (min_le_right _ _)
  have h := Real.rpow_le_rpow hε.le hroot hp.le
  rw [← Real.rpow_mul (hn n ω),one_div_mul_cancel hp.ne',Real.rpow_one] at h
  exact h

/-- The expectation of the printed geometrically weighted metric tends
to zero when every bounded coordinate does. The exchange of expectation
and the infinite sum is justified by its summable geometric bound. -/
theorem weighted_bounded_coordinate_mean_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → ℕ → Ω → ℝ) (hm : ∀ n j, Measurable (R n j))
    (hb : ∀ n j ω, 0 ≤ R n j ω ∧ R n j ω ≤ 1)
    (hl : ∀ j, Tendsto (fun n => ∫ ω, R n j ω ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ∑' j : ℕ, (1/2:ℝ)^(j+1)*R n j ω ∂P) atTop (𝓝 0) := by
  let w := fun j : ℕ => (1/2:ℝ)^(j+1)
  let a := fun n j => w j * ∫ ω, R n j ω ∂P
  have hRi n j : Integrable (R n j) P := Integrable.of_bound (hm n j).aestronglyMeasurable 1
    (.of_forall (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hb n j ω).1]; exact (hb n j ω).2))
  have hab n j : 0 ≤ a n j ∧ a n j ≤ w j := by
    have hp : 0 ≤ ∫ ω, R n j ω ∂P := integral_nonneg (fun ω => (hb n j ω).1)
    have h1 : (∫ ω, R n j ω ∂P) ≤ 1 := by
      have h := integral_mono (hRi n j) (integrable_const (1:ℝ)) (fun ω => (hb n j ω).2)
      simpa using h
    exact ⟨mul_nonneg (by dsimp [w]; positivity) hp,
      (mul_le_mul_of_nonneg_left h1 (by dsimp [w]; positivity)).trans_eq (mul_one _)⟩
  have has n : Summable (a n) := Summable.of_nonneg_of_le (fun j => (hab n j).1)
    (fun j => (hab n j).2) path_weights_summable
  have he n : (∫ ω, ∑' j : ℕ, w j*R n j ω ∂P) = ∑' j, a n j := by
    have hnorm j : (∫ ω, ‖w j*R n j ω‖ ∂P) = a n j := by
      have hf : (fun ω => ‖w j*R n j ω‖) = fun ω => w j*R n j ω := by
        funext ω
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by dsimp [w]; positivity) (hb n j ω).1)]
      rw [hf,integral_const_mul]
    have hn : Summable (fun j => ∫ ω, ‖w j*R n j ω‖ ∂P) := by
      simpa only [hnorm] using has n
    have h := integral_tsum_of_summable_integral_norm (fun j => (hRi n j).const_mul (w j)) hn
    rw [← h]
    simp only [integral_const_mul,a]
  have ha n : Integrable (a n) Measure.count := integrable_count_iff.2 (has n).norm
  have hc j : Tendsto (fun n => a n j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (hl j).const_mul (w j)
  have hs := tendsto_integral_of_dominated_convergence (μ := Measure.count) w
    (fun n => (ha n).aestronglyMeasurable) (integrable_count_iff.2 path_weights_summable.norm)
    (fun n => .of_forall (fun j => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hab n j).1]
      exact (hab n j).2)) (f := fun _ : ℕ => (0:ℝ)) (.of_forall hc)
  have hcount n : (∫ j, a n j ∂Measure.count) = ∑' j, a n j := by
    rw [integral_countable (ha n)]
    simp [Measure.real,Measure.count_singleton]
  change Tendsto (fun n => ∫ ω, ∑' j : ℕ, w j*R n j ω ∂P) atTop (𝓝 0)
  simpa only [he,hcount,integral_zero] using hs

/-- The probability estimates proved by local_step_density imply
convergence for rho_A itself, including the pth root in the manuscript. -/
theorem expected_integrand_metric_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → ℕ → Ω → ℝ) (hm : ∀ n j, Measurable (R n j))
    (hn : ∀ n j ω, 0 ≤ R n j ω) (p : ℝ) (hp : 0 < p)
    (hl : ∀ j (ε : ℝ), 0 < ε → Tendsto (fun n => P {ω | ε ≤ R n j ω}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ∑' j : ℕ, (1/2:ℝ)^(j+1)*min 1 ((R n j ω)^(1/p)) ∂P)
      atTop (𝓝 0) := by
  apply weighted_bounded_coordinate_mean_limit P _
    (fun n j => measurable_const.min ((hm n j).pow_const (1/p)))
    (fun n j ω => ⟨le_min zero_le_one (Real.rpow_nonneg (hn n j ω) _),min_le_left _ _⟩)
  intro j
  exact truncated_root_mean_limit P (fun n => R n j) (fun n => hm n j) (fun n => hn n j) p hp (hl j)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.truncated_root_mean_limit
#print axioms Asakura.Chapter2Complete.weighted_bounded_coordinate_mean_limit
#print axioms Asakura.Chapter2Complete.expected_integrand_metric_limit
