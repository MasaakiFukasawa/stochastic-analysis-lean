import Chapter7StoppedSpaceOrderAE
import Chapter7IntervalEventMeasurable

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000

/-- A short future-path event at one stopping time is measurable at a
later stopping time, provided the latter is at least that far ahead. -/
theorem stay_event_at_next_stop
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    (F : ℝ≥0 → MeasurableSpace Ω) (hF : Monotone F) (hl : ∀ t,F t ≤ m)
    (hn : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t,Measurable[F t] (B t))
    (hc : ∀ w,Continuous (fun t => B t w))
    (τ σ : Ω → ℝ≥0)
    (hτ : ∀ t,MeasurableSet[F t] {w | τ w ≤ t})
    (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t})
    (δ : ℝ≥0) (hgap : ∀ᵐ w ∂P,τ w+δ ≤ σ w) :
    MeasurableSet[writtenStoppedSpace m F σ hσ]
      {w | ∀ r : ℝ≥0,r ≤ δ → |B (τ w+r) w-B (τ w) w| ≤ 1} := by
  have hτσ : τ ≤ᵐ[P] σ := hgap.mono fun w hw => (le_add_right le_rfl).trans hw
  have hBτ := (finite_stopped_sampling m F hF hl B hm hc τ hτ).mono
    (stopped_space_mono_ae P F hl hn τ σ hτ hσ hτσ) le_rfl
  apply interval_stay_measurable _ _
    (fun w => ((hc w).comp (continuous_const.add continuous_id)).sub continuous_const) δ
  intro r hr
  have hτr := nnreal_stopping_add F hF τ hτ r
  have hle : (fun w => τ w+r) ≤ᵐ[P] σ := hgap.mono fun w hw =>
    (show τ w+r ≤ τ w+δ from by exact_mod_cast (show (τ w:ℝ)+(r:ℝ) ≤ (τ w:ℝ)+(δ:ℝ) from by exact add_le_add le_rfl hr)).trans hw
  have hBτr := (finite_stopped_sampling m F hF hl B hm hc _ hτr).mono
    (stopped_space_mono_ae P F hl hn _ σ hτr hσ hle) le_rfl
  exact hBτr.sub hBτ

end Asakura.Chapter7
