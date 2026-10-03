import Chapter2CumulativeIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 700000

/-- The endpoint convention in elementary predictable integrands agrees
with increments of the cumulative integral because the measure has no atoms. -/
theorem cumulative_increment_elementary_test
    (μ : Measure ℝ) [NullSingletonClass μ] (g : ℝ → ℝ)
    (hg : Integrable g μ) (s t z : ℝ) (hst : s ≤ t) :
    z * ((∫ x in Iic t, g x ∂μ) - ∫ x in Iic s, g x ∂μ) =
      ∫ x, ((Ico s t).indicator (fun _ => z) x) * g x ∂μ := by
  have hd : (∫ x in Iic t, g x ∂μ) - ∫ x in Iic s, g x ∂μ =
      ∫ x in Ioc s t, g x ∂μ := by
    rw [← setIntegral_sdiff measurableSet_Iic hg.integrableOn (Iic_subset_Iic.2 hst)]
    have he : Iic t \ Iic s = Ioc s t := by
      ext x
      simp only [Set.mem_sdiff,mem_Iic,mem_Ioc,not_le]
      tauto
    rw [he]
  rw [hd,← integral_Ico_eq_integral_Ioc,← integral_const_mul]
  have he : (fun x => ((Ico s t).indicator (fun _ => z) x) * g x) =
      (Ico s t).indicator (fun x => z*g x) := by
    funext x
    by_cases hx : x ∈ Ico s t <;> simp [Set.indicator,hx]
  rw [he,integral_indicator measurableSet_Ico]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.cumulative_increment_elementary_test
