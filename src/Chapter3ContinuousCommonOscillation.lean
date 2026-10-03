import Chapter3QVDefectEstimate
import Chapter2CommonTimeEquality

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Turn the deterministic-time essential bounds defining the partition
into one common pathwise bound, including its stopped terminal value. -/
theorem continuous_stopped_increment_common_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (X : ClosedTime T → Ω → ℝ) (hX : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (σ τ : Ω → ClosedTime T) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hτtop : ∀ ω, τ ω < ⊤) (δ : ℝ)
    (hb : ∀ t, t < ⊤ → ∀ᵐ ω ∂P,
      ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ) :
    ∀ᵐ ω ∂P, ∀ t, ‖X (min (τ ω) t) ω-X (min (σ ω) t) ω‖ ≤ δ := by
  let D := fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω
  have hc (ω) : Continuous (fun t => D t ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((hX ω _ ((min_le_left _ _).trans_lt (hτtop ω))).comp
      (continuous_const.min continuous_id).continuousAt).sub
      ((hX ω _ ((min_le_left _ _).trans_lt ((hστ ω).trans_lt (hτtop ω)))).comp
        (continuous_const.min continuous_id).continuousAt)
  letI : Nonempty (Iio (⊤ : ClosedTime T)) := ⟨⟨⊥,hT⟩⟩
  have he := continuous_process_common_time_equality P
    (fun t : Iio (⊤ : ClosedTime T) => fun ω => min ‖D t.val ω‖ δ)
    (fun t : Iio (⊤ : ClosedTime T) => fun ω => ‖D t.val ω‖)
    (fun ω => (((hc ω).comp continuous_subtype_val).norm).min continuous_const)
    (fun ω => ((hc ω).comp continuous_subtype_val).norm)
    (fun t => (hb t.val t.property).mono fun ω h => min_eq_left h)
  filter_upwards [he] with ω hω
  intro t
  have hh := hω ⟨min (τ ω) t,(min_le_left _ _).trans_lt (hτtop ω)⟩
  have hb' : ‖D (min (τ ω) t) ω‖ ≤ δ := by
    rw [← hh]
    exact min_le_right _ _
  simpa only [D,← min_assoc,min_self,min_eq_left (hστ ω)] using hb'

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_stopped_increment_common_bound
