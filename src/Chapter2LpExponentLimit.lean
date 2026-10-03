import Chapter2ClippedLp

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 700000

/-- Holder's estimate transfers L2 approximation to every smaller
positive exponent on the finite random measure. -/
theorem finite_measure_lower_exponent_limit
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (f : ℕ → S → ℝ) (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 2)
    (hlim : Tendsto (fun n => eLpNorm' (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm' (f n) p μ) atTop (𝓝 0) := by
  have hr : 0 ≤ 1/p-1/2 := by
    have h := one_div_le_one_div_of_le hp hp2
    linarith
  have hfin : μ univ ^ (1/p-1/2) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr (measure_ne_top μ univ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => eLpNorm' (f n) 2 μ * μ univ ^ (1/p-1/2)) atTop (𝓝 0) from by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr hfin))
  · exact fun n => bot_le
  · exact fun n => eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp hp2 (hm n)

/-- The p>2 estimate transfers convergence of square integrals to
convergence of pth-power integrals for uniformly bounded errors. -/
theorem bounded_higher_exponent_integral_limit
    {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (f : ℕ → S → ℝ) (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (h2 : ∀ n, Integrable (fun x => f n x ^ 2) μ)
    (C p : ℝ) (hC : 0 ≤ C) (hp : 2 ≤ p)
    (hb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ C)
    (hlim : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |f n x| ^ p ∂μ) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => C^(p-2) * ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (C^(p-2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
  · exact fun n => integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  · exact fun n => (bounded_rpow_integral_le_square μ (f n) (hm n) (h2 n) C p hC hp (hb n)).2

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.finite_measure_lower_exponent_limit
#print axioms Asakura.Chapter2Complete.bounded_higher_exponent_integral_limit
