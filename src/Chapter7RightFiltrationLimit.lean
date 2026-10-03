import Chapter2WrittenLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.Chapter2Written
set_option maxHeartbeats 1000000

/-- The backward conditional-expectation theorem used to pass from F_(T_s)
to the right-continuous time-changed filtration. Path continuity identifies
the L1 limit directly; no almost-sure convergent subsequence is taken. -/
theorem time_changed_right_filtration_identity
    {Ω S : Type*} {m : MeasurableSpace Ω} [TopologicalSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hG : Antitone G) (hle : ∀ n,G n ≤ m)
    (X : S → Ω → ℝ) (hc : ∀ w,Continuous (fun t => X t w))
    (s : S) (r : ℕ → S) (hr : Tendsto r atTop (𝓝 s))
    (Y : Ω → ℝ) (hmY : Measurable[m] Y) (hiY : Integrable Y P)
    (hmX : Measurable[m] (X s))
    (he : ∀ n,P[Y|G n] =ᵐ[P] X (r n)) :
    P[Y|⨅ n,G n] =ᵐ[P] X s := by
  apply Filter.EventuallyEq.symm
  apply written_backward_limit_identification G hG hle hmY hiY hmX.aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr he] with w hw
  have ht := (hc w).continuousAt.tendsto.comp hr
  exact ht.congr (fun n => (hw n).symm)

end Asakura.Chapter7
