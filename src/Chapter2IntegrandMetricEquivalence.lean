import Chapter2IntegrandMetricLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The converse half of the manuscript's rho_A/probability equivalence,
including the pth root. No monotonicity in the horizon index is needed. -/
theorem integrand_probability_of_metric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℕ → ℕ → Ω → ℝ) (hm : ∀ n j, Measurable (R n j))
    (hn : ∀ n j ω, 0 ≤ R n j ω) (p : ℝ) (hp : 0 < p)
    (hl : Tendsto (fun n => ∫ ω, ∑' j : ℕ, (1/2:ℝ)^(j+1)*min 1 ((R n j ω)^(1/p)) ∂P)
      atTop (𝓝 0)) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ R n j ω}) atTop (𝓝 0) := by
  let W := fun j : ℕ => (1/2:ℝ)^(j+1)
  let D := fun n ω => ∑' j : ℕ, W j*min 1 ((R n j ω)^(1/p))
  have ha n ω k : 0 ≤ W k*min 1 ((R n k ω)^(1/p)) :=
    mul_nonneg (by dsimp [W]; positivity) (le_min zero_le_one (Real.rpow_nonneg (hn n k ω) _))
  have hb n ω k : W k*min 1 ((R n k ω)^(1/p)) ≤ W k := by
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by dsimp [W]; positivity)).trans_eq (mul_one _)
  have hs n ω : Summable (fun k => W k*min 1 ((R n k ω)^(1/p))) :=
    Summable.of_nonneg_of_le (ha n ω) (hb n ω) path_weights_summable
  have hD n : Measurable (D n) := by
    exact Measurable.tsum (fun k => measurable_const.mul (measurable_const.min ((hm n k).pow_const _)))
  have hD0 n ω : 0 ≤ D n ω := tsum_nonneg (ha n ω)
  have hD1 n ω : D n ω ≤ 1 := by
    rw [← path_weights_sum]
    exact (hs n ω).tsum_le_tsum (hb n ω) path_weights_summable
  have hDi n : Integrable (D n) P := Integrable.of_bound (hD n).aestronglyMeasurable 1
    (.of_forall fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hD0 n ω)]; exact hD1 n ω)
  let δ := W j*min 1 (ε^(1/p))
  have hδ : 0 < δ := mul_pos (by dsimp [W]; positivity) (lt_min zero_lt_one (Real.rpow_pos_of_pos hε _))
  have hbound n : P {ω | ε ≤ R n j ω} ≤ ENNReal.ofReal ((∫ ω, D n ω ∂P)/δ) := by
    have hmark := meas_ge_le_lintegral_div (μ := P) (hD n).ennreal_ofReal.aemeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hδ) ENNReal.ofReal_ne_top
    have hinc : {ω | ε ≤ R n j ω} ⊆ {ω | ENNReal.ofReal δ ≤ ENNReal.ofReal (D n ω)} := by
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_left (min_le_min_left 1
        (Real.rpow_le_rpow hε.le hω (by positivity))) (by dsimp [W]; positivity)).trans
        ((hs n ω).le_tsum j (fun k _ => ha n ω k))
    apply (measure_mono hinc).trans
    rw [← ofReal_integral_eq_lintegral_ofReal (hDi n) (.of_forall (hD0 n)),
      ← ENNReal.ofReal_div_of_pos hδ] at hmark
    exact hmark
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hl.div_const δ)
  simp only [zero_div,ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.integrand_probability_of_metric
