import Chapter7BrownianRecurrenceAll

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2200000

/-- Countably many recurrence assertions give one event on which every
real level is reached, including levels chosen from the observed path. -/
theorem brownian_all_levels
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) :
    ∀ᵐ w ∂P,∀ x : ℝ,∃ r : ℝ,0 ≤ r ∧ B.W 0 (realTimeClamp r) w = x := by
  have hi : ∀ z : ℤ,∀ᵐ w ∂P,∃ r : ℝ,0 ≤ r ∧ B.W 0 (realTimeClamp r) w = z := by
    intro z
    filter_upwards [brownian_hits_zero P B (-(z:ℝ))] with w hw
    obtain ⟨r,hr,he⟩ := hw
    exact ⟨r,hr,by linarith⟩
  filter_upwards [ae_all_iff.mpr hi] with w hw
  let f := fun r : ℝ => B.W 0 (realTimeClamp (max 0 r)) w
  have hc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (((B.martingale 0).path P B.F w _ (changed_time_finite _ (le_max_left _ _))).comp
      real_time_clamp_continuous.continuousAt).comp (continuous_const.max continuous_id).continuousAt
  have hlevels : ∀ z : ℤ,∃ t : ℝ,0 ≤ t ∧ f t = z := by
    intro z
    obtain ⟨r,hr,he⟩ := hw z
    exact ⟨r,hr,by simpa only [f,max_eq_right hr] using he⟩
  intro x
  obtain ⟨r,hr,he⟩ := continuous_path_hits_all_levels f hc hlevels x
  exact ⟨r,hr,by simpa only [f,max_eq_right hr] using he⟩

end Asakura.Chapter7
