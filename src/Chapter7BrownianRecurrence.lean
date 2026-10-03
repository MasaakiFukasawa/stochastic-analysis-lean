import Chapter7BrownianExitMoments
import Chapter7ExitProbabilityBound

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000

/-- A Brownian path starting to the right of zero reaches zero almost
surely. The proof uses capped exits, then sends the time cap and the
upper spatial boundary to infinity, exactly as in the stopped-moment
argument in the manuscript. -/
theorem brownian_hits_zero_from_nonnegative
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (x : ℝ) (hx : 0 ≤ x) :
    ∀ᵐ w ∂P,∃ r : ℝ,0 ≤ r ∧ x+B.W 0 (realTimeClamp r) w = 0 := by
  let E := {w | ∀ r : ℝ,0 ≤ r → x+B.W 0 (realTimeClamp r) w ≠ 0}
  have hbound (R : ℝ) (hR : 0 < R) (hxR : x ≤ R) (c : ℝ) (hc : 0 < c) :
      P.real E ≤ x/R+R^2/c := by
    obtain ⟨τ,hτ,hτc,hb,hboundary⟩ := brownian_capped_exit_stop P B x R c hx hxR hc.le
    obtain ⟨hxi,hci,hxm,hcm⟩ := brownian_exit_moments P B x R c hc.le τ hτ hτc hb
    apply exit_probability_bound P _ _ hxi hci
      (hb.mono (fun w h => by simpa only [min_top_right,Pi.zero_apply] using (h ⊤).1))
      (ae_of_all _ fun w => by
        change 0 ≤ B.C 0 0 (τ w) w
        rw [brownian_clock_at_finite B _ (lt_of_le_of_lt (hτc w) (changed_time_finite c hc.le))]
        exact (halfTimeReal (τ w)).property) x R c hR hc hxm hcm E
    filter_upwards [hboundary] with w hw
    intro hE
    by_cases hlt : τ w < realTimeClamp c
    · obtain hz | hz := hw hlt
      · obtain ⟨r,hr,_,he⟩ := finite_closed_time_real (τ w) (lt_trans hlt (changed_time_finite c hc.le))
        exact (hE r hr (by simpa only [he] using hz)).elim
      · exact Or.inl hz.ge
    · have he : τ w = realTimeClamp c := le_antisymm (hτc w) (le_of_not_gt hlt)
      right
      rw [he,B.diagonal_clock 0 w c hc.le]
  have hRbound (R : ℝ) (hR : 0 < R) (hxR : x ≤ R) : P.real E ≤ x/R := by
    have hlim : Tendsto (fun c : ℝ => x/R+R^2/c) atTop (𝓝 (x/R)) := by
      simpa only [add_zero] using tendsto_const_nhds.add
        (show Tendsto (fun c : ℝ => R^2/c) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_id)
    exact ge_of_tendsto hlim ((eventually_gt_atTop (0:ℝ)).mono fun c hc => hbound R hR hxR c hc)
  have hz : P.real E ≤ 0 := by
    have hlim : Tendsto (fun R : ℝ => x/R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    apply ge_of_tendsto hlim
    filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop x] with R hR hxR
    exact hRbound R hR hxR
  have hzero : P E = 0 := (ENNReal.toReal_eq_zero_iff (P E)).mp (le_antisymm hz ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  convert hzero using 1
  congr 1
  ext w
  simp [E]

end Asakura.Chapter7
