import Chapter2VariationIntegralFormula

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem finite_prefix_time_of_real
    {T : EReal} [Fact (0 ≤ T)] (d r : ℝ) (hd : 0 ≤ d)
    (hr : r ∈ Icc 0 d) (hdT : (d:EReal) ≤ T) :
    (finitePrefixTime d hd (realTimeClamp (T := T) r)).val = r := by
  change (min (realTimeClamp r : EReal) (d:EReal)).toReal = r
  rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT),
    min_eq_left (EReal.coe_le_coe hr.2),EReal.toReal_coe]

theorem signed_cumulative_interval_clamp
    (ν : SignedMeasure ℝ) (H : ℝ → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hs : ∀ᵐ r ∂ν.totalVariation, r ∈ Ioc 0 d) (t : ℝ) :
    signedCumulative ν H (intervalClamp 0 d hd t) = signedCumulative ν H t := by
  apply signed_integral_congr_of_absolute_continuity ν.totalVariation ν (by rfl)
  filter_upwards [hs] with r hr
  have he : r ≤ intervalClamp 0 d hd t ↔ r ≤ t := by
    by_cases ht0 : t ≤ 0
    · have hclip : intervalClamp 0 d hd t = 0 := by
        simp only [intervalClamp,projIcc_of_le_left hd ht0]
      rw [hclip]
      exact iff_of_false (not_le.mpr hr.1) (not_le.mpr (ht0.trans_lt hr.1))
    · by_cases hdt : d ≤ t
      · have hclip : intervalClamp 0 d hd t = d := by
          simp only [intervalClamp,projIcc_of_right_le hd hdt]
        rw [hclip]
        exact iff_of_true hr.2 (hr.2.trans hdt)
      · rw [intervalClamp_eq 0 d hd ⟨(le_of_not_ge ht0),(le_of_not_ge hdt)⟩]
  simp only [indicator_apply,mem_Iic,he]

/-- The finite-prefix process formula gives its real cumulative integral
at every clipped real argument, including arguments outside the interval. -/
theorem variation_sample_cumulative_identification
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (ν : SignedMeasure ℝ) (H : ℝ → ℝ) (I : ClosedTime T → ℝ)
    (hs : ∀ᵐ r ∂ν.totalVariation, r ∈ Ioc 0 d)
    (he : ∀ t, I (min (realTimeClamp d) t) =
      signedCumulative ν H (finitePrefixTime d hd t).val) :
    ∀ r, I (realTimeClamp (intervalClamp 0 d hd r)) = signedCumulative ν H r := by
  intro r
  have hr := intervalClamp_mem 0 d hd r
  have hh := he (realTimeClamp (intervalClamp 0 d hd r))
  rw [min_eq_right (real_time_clamp_mono hr.2),finite_prefix_time_of_real d _ hd hr hdT] at hh
  exact hh.trans (signed_cumulative_interval_clamp ν H d hd hs r)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.variation_sample_cumulative_identification
