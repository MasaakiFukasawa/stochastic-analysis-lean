import FullAuditBoundedProcess
import FullAuditStoppedSquareEnergy
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
  (hF : Monotone F) (hle : ∀ t, F t ≤ m)

include hF hle

/-- Closure under stopping, including adaptedness, square moments, continuous
paths, the actual CE martingale identity, and the zero initial condition. -/
theorem continuous_m2_stopped (X : ClosedTime T → Ω → ℝ)
    (hX : ContinuousM2Witness P F X)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    ContinuousM2Witness P F (fun t ω => X (min (τ ω) t) ω) := by
  have hr (ω : Ω) (t : ClosedTime T) : ContinuousWithinAt (fun s => X s ω) (Ici t) t :=
    (hX.path ω).continuousAt.continuousWithinAt
  have hi := fun t => (hX.moment t).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hclosed := fun t => (hX.martingale t ⊤ le_top).symm
  have htop := (hX.adapted ⊤).mono (hle ⊤) le_rfl
  have hm := stopped_min_value_measurable F hF τ hτ X hX.adapted hr
  have hce (t) : (fun ω => X (min (τ ω) t) ω) =ᵐ[P]
      P[X ⊤ | writtenStoppedSpace m F (fun ω => min (τ ω) t)
        ((written_stopping_min_max F τ (fun _ => t) hτ
          (fun s => by by_cases h : t ≤ s <;> simp [h])).1)] := by
    exact continuous_closed_optional_written P (Fact.out : 0 ≤ T) F hF hle
      _ _ X hX.adapted hr htop (hi ⊤) hclosed
  have hclosedτ (t) := stopped_value_conditional P F hF hle X hX.adapted hi hX.path hX.martingale τ hτ t
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · intro t
    apply MemLp.ae_eq (hce t).symm
    exact (hX.moment ⊤).condExp (by norm_num : (1:ℝ≥0∞) ≤ 2)
  · intro ω
    exact (hX.path ω).comp (continuous_const.min continuous_id)
  · intro s t hst
    have hs := hclosedτ s
    have ht := hclosedτ t
    simpa only [min_comm] using (condExp_congr_ae ht.symm).trans
      ((condExp_condExp_of_le (hF hst) (hle t)).trans hs)
  · simpa only [min_bot_right] using hX.initial

/-- A bounded continuous martingale stays in the manuscript's M_infty
space after stopping; the terminal L_infty condition is sufficient. -/
theorem bounded_martingale_stopped (X : boundedMProcess P F)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    (fun t ω => X.val (min (τ ω) t) ω) ∈ boundedMProcess P F := by
  refine ⟨continuous_m2_stopped P F hF hle X.val X.property.1 τ hτ, ?_⟩
  intro t
  have hmin := (written_stopping_min_max F τ (fun _ => t) hτ
    (fun s => by by_cases h : t ≤ s <;> simp [h])).1
  have h := continuous_closed_optional_written P (Fact.out : 0 ≤ T) F hF hle
    (fun ω => min (τ ω) t) hmin X.val X.property.1.adapted
    (fun ω s => (X.property.1.path ω).continuousAt.continuousWithinAt)
    ((X.property.1.adapted ⊤).mono (hle ⊤) le_rfl)
    ((X.property.1.moment ⊤).integrable (by norm_num))
    (fun s => (X.property.1.martingale s ⊤ le_top).symm)
  apply MemLp.ae_eq h.symm
  exact (X.property.2 ⊤).condExp (by simp : (1:ℝ≥0∞) ≤ ∞)

/-- Optional sampling plus an actual stopped-path bound promotes an
integrable continuous martingale to a bounded stopped martingale. -/
theorem bounded_stop_of_integrable_martingale
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t)) (hi : ∀ t, Integrable (X t) P)
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (hz : X ⊥ =ᵐ[P] 0)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (K : ℝ) (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X (min (τ ω) t) ω‖ ≤ K) :
    (fun t ω => X (min (τ ω) t) ω) ∈ boundedMProcess P F := by
  have hms := stopped_min_value_measurable F hF τ hτ X hm
    (fun ω t => (hc ω).continuousAt.continuousWithinAt)
  have hboundLp (t) : MemLp (fun ω => X (min (τ ω) t) ω) ∞ P :=
    memLp_top_of_bound ((hms t).mono (hle t) le_rfl).aestronglyMeasurable K (hbound t)
  refine ⟨⟨hms, fun t => (hboundLp t).mono_exponent le_top,
    fun ω => (hc ω).comp (continuous_const.min continuous_id), ?_, ?_⟩, hboundLp⟩
  · intro s t hst
    have hs := stopped_value_conditional P F hF hle X hm hi hc hM τ hτ s
    have ht := stopped_value_conditional P F hF hle X hm hi hc hM τ hτ t
    simpa only [min_comm] using (condExp_congr_ae ht.symm).trans
      ((condExp_condExp_of_le (hF hst) (hle t)).trans hs)
  · simpa only [min_bot_right] using hz

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_m2_stopped
#print axioms Asakura.Chapter2Complete.bounded_martingale_stopped

#print axioms Asakura.Chapter2Complete.bounded_stop_of_integrable_martingale
