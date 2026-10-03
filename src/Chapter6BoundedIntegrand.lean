import Chapter6MeasurableCovarianceDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6

lemma bounded_time_integrable (H : ℝ → ℝ) (hm : Measurable H)
    (K : ℝ) (hk : ∀ r,|H r| ≤ K) (b : ℝ) (hb : 0 ≤ b) :
    IntervalIntegrable H volume 0 b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mpr
  exact Integrable.of_bound hm.aestronglyMeasurable K (ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using hk r)

lemma bounded_product_time_integrable (H G : ℝ → ℝ) (hm : Measurable H) (hgm : Measurable G)
    (K : ℝ) (hK : 0 ≤ K) (hk : ∀ r,|H r| ≤ K) (hg : ∀ r,|G r| ≤ K)
    (b : ℝ) (hb : 0 ≤ b) : IntervalIntegrable (fun r => H r*G r) volume 0 b := by
  apply bounded_time_integrable _ (hm.mul hgm) (K^2) _ b hb
  intro r
  change |H r * G r| ≤ K^2
  rw [abs_mul,pow_two]
  exact mul_le_mul (hk r) (hg r) (abs_nonneg _) hK

end Asakura.Chapter6
