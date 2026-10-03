import Chapter2ContinuousLocalizers
import Chapter2SquareIntegrableStop

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The zero-stopped-mean characterization in Exercise reploc. The
boundedness condition is the existence of an essential uniform path bound. -/
theorem local_iff_zero_bounded_stopped_means
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (hz : X ⊥ =ᵐ[P] 0) :
    LocalMProcessWitness P F X ↔
      ∀ (σ : Ω → ClosedTime T), (∀ t, MeasurableSet[F t] {ω | σ ω ≤ t}) →
      (∀ ω, σ ω < ⊤) → ∀ K : ℝ,
      (∀ᵐ ω ∂P, ∀ t, ‖X (min (σ ω) t) ω‖ ≤ K) →
      (∫ ω, X (σ ω) ω ∂P) = 0 := by
  constructor
  · intro hX σ hσ hσtop K hb
    have hM := (bounded_local_stop_is_bounded_martingale P F hF hle X hX σ hσ hσtop K hb).1
    have hh := integral_congr_ae ((hM.martingale ⊥ ⊤ le_top).trans hM.initial)
    rw [integral_condExp (hle ⊥)] at hh
    simpa only [min_top_right,Pi.zero_apply,integral_zero] using hh
  · intro hmeans
    obtain ⟨σ,hs,hsm,hst,hsc,hbound⟩ :=
      halfopen_continuous_bounded_localizers P hT F hF X hm hc hz
    have hr (ω t) : ContinuousWithinAt (fun s => X s ω) (Ici t) t := by
      by_cases ht : t < ⊤
      · exact (hc ω t ht).continuousWithinAt
      · have he : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
        subst t
        simp only [Ici_top]
        exact continuousWithinAt_singleton
    refine ⟨σ,hs,hsm,hst,hsc,?_⟩
    intro n
    let Y := fun t ω => X (min (σ n ω) t) ω
    have hYm := stopped_min_value_measurable F hF (σ n) (hs n) X hm hr
    have hYc (ω) : Continuous (fun t => Y t ω) := by
      apply continuous_iff_continuousAt.2
      intro t
      exact (hc ω _ ((min_le_left _ _).trans_lt (hst n ω))).comp
        (continuous_const.min continuous_id).continuousAt
    have hYinf (t) : MemLp (Y t) ∞ P :=
      memLp_top_of_bound ((hYm t).mono (hle t) le_rfl).aestronglyMeasurable (n:ℝ)
        ((hbound n).mono fun ω hω => hω t)
    refine ⟨⟨hYm,fun t => (hYinf t).mono_exponent le_top,hYc,?_,?_⟩,hYinf⟩
    · apply martingale_of_zero_stopped_means P F hF hle Y hYm
        (fun t => (hYinf t).integrable (by simp))
      intro ρ hρ
      have hσρ := (written_stopping_min_max F (σ n) ρ (hs n) hρ).1
      apply hmeans (fun ω => min (σ n ω) (ρ ω)) hσρ
        (fun ω => (min_le_left _ _).trans_lt (hst n ω)) (n:ℝ)
      filter_upwards [hbound n] with ω hω
      intro t
      simpa only [min_assoc] using hω (min (ρ ω) t)
    · simpa only [Y,min_bot_right] using hz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_iff_zero_bounded_stopped_means
