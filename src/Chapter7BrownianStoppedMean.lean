import Chapter7BrownianExitStop
import Chapter5DominatedLocalMean

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2600000

/-- The first stopped moment is obtained from the actual Brownian local
martingale and a bounded stopped path, without assuming optional sampling. -/
theorem brownian_bounded_stop_mean
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (τ : Ω → HalfClosedTime)
    (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w ≤ t})
    (hfinite : ∀ w,τ w < ⊤) (K : ℝ)
    (hb : ∀ᵐ w ∂P,∀ t,|B.W 0 (min (τ w) t) w| ≤ K) :
    (∫ w,B.W 0 (τ w) w ∂P) = 0 := by
  have hl := (B.martingale 0).stopped P B.F B.mono B.le τ hτ
  obtain ⟨_,hc⟩ := (B.martingale 0).stopped_regular P B.F B.mono B.le τ hτ hfinite
  have hm := dominated_local_terminal_mean P B.F B.le _ hl hc
    (fun _ => K) (integrable_const K) hb
  simpa only [min_top_right] using hm

/-- The stopped quadratic identity is likewise a consequence of the
actual covariance defect B²-C being a local martingale. -/
theorem brownian_bounded_stop_square
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (τ : Ω → HalfClosedTime)
    (hτ : ∀ t,MeasurableSet[B.F t] {w | τ w ≤ t})
    (hfinite : ∀ w,τ w < ⊤) (K : ℝ)
    (hb : ∀ᵐ w ∂P,∀ t,
      |B.W 0 (min (τ w) t) w * B.W 0 (min (τ w) t) w -
        B.C 0 0 (min (τ w) t) w| ≤ K) :
    (∫ w,B.W 0 (τ w) w * B.W 0 (τ w) w - B.C 0 0 (τ w) w ∂P) = 0 := by
  have hl := (B.cov 0 0).defect.stopped P B.F B.mono B.le τ hτ
  obtain ⟨_,hc⟩ := (B.cov 0 0).defect.stopped_regular P B.F B.mono B.le τ hτ hfinite
  have hm := dominated_local_terminal_mean P B.F B.le _ hl hc
    (fun _ => K) (integrable_const K) hb
  simpa only [min_top_right] using hm

end Asakura.Chapter7
