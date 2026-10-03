import Chapter2ExplicitLocalizers
import Chapter2LocalZeroMeanCriterion

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Cutting an infimum off at u only uses the set strictly below u. -/
theorem min_infimum_eq_of_agree_below
    {α : Type*} [CompleteLinearOrder α] (S R : Set α) (u : α)
    (he : ∀ t, t < u → (t ∈ S ↔ t ∈ R)) :
    min (sInf S) u = min (sInf R) u := by
  have hle (S R : Set α) (he : ∀ t, t < u → (t ∈ S ↔ t ∈ R)) :
      min (sInf S) u ≤ min (sInf R) u := by
    apply le_min _ (min_le_right _ _)
    apply le_sInf
    intro t ht
    by_cases htu : t < u
    · exact (min_le_left _ _).trans (sInf_le ((he t htu).2 ht))
    · exact (min_le_right _ _).trans (le_of_not_gt htu)
  exact le_antisymm (hle S R he) (hle R S (fun t ht => (he t ht).symm))

/-- The manuscript's exact level hitting times, including its prescribed
deterministic cutoffs, are bounded localizers for every continuous adapted
process starting at zero. No continuity at T is assumed. -/
theorem canonical_continuous_localizers
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (hz : X ⊥ =ᵐ[P] 0)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n) :
    let σ := fun (n : ℕ) (ω : Ω) => min (sInf {t | (n:ℝ) ≤ |X t ω|}) (u n)
    (∀ n t, MeasurableSet[F t] {ω | σ n ω ≤ t}) ∧
    (∀ ω, Monotone (fun n => σ n ω)) ∧ (∀ n ω, σ n ω < ⊤) ∧
    (∀ ω t, t < ⊤ → ∃ n, t < σ n ω) ∧
    (∀ n, ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ n ω) t) ω‖ ≤ (n:ℝ)) := by
  have hτ n t : MeasurableSet[F t] {ω : Ω | u n ≤ t} := by
    by_cases ht : u n ≤ t <;> simp [ht]
  have had n t : Measurable[F t] (fun ω => X (min (u n) t) ω) :=
    (hm _).mono (hF (min_le_right _ _)) le_rfl
  have hcont n ω : Continuous (fun t => X (min (u n) t) ω) := by
    apply continuous_iff_continuousAt.2
    intro t
    exact (hc ω _ ((min_le_left _ _).trans_lt (hut n))).comp
      (continuous_const.min continuous_id).continuousAt
  have hzero n : (fun ω => X (min (u n) ⊥) ω) =ᵐ[P] 0 := by
    simpa only [min_bot_right] using hz
  have hs := explicit_continuous_process_bounded_localizers P F hF X (fun n _ => u n)
    hτ (fun _ => hu) (fun n _ => hut n) (fun _ => huc) had hcont hzero
  have he (n : ℕ) (ω : Ω) : min (sInf {t | (n:ℝ) ≤ |X (min (u n) t) ω|}) (u n) =
      min (sInf {t | (n:ℝ) ≤ |X t ω|}) (u n) := by
    apply min_infimum_eq_of_agree_below
    intro t ht
    change ((n:ℝ) ≤ |X (min (u n) t) ω|) ↔ ((n:ℝ) ≤ |X t ω|)
    rw [min_eq_right ht.le]
  dsimp only at hs ⊢
  simpa only [he] using hs

/-- Exercise reploc, conditions i and ii, for the exact hitting-time
sequence specified in the manuscript. Combined with the checked
zero-stopped-mean criterion this proves all three equivalences. -/
theorem local_iff_canonical_bounded_stops
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (hz : X ⊥ =ᵐ[P] 0)
    (u : ℕ → ClosedTime T) (hu : Monotone u) (hut : ∀ n, u n < ⊤)
    (huc : ∀ t, t < ⊤ → ∃ n, t < u n) :
    let σ := fun (n : ℕ) (ω : Ω) => min (sInf {t | (n:ℝ) ≤ |X t ω|}) (u n)
    LocalMProcessWitness P F X ↔ ∀ n, (fun t ω => X (min (σ n ω) t) ω) ∈ boundedMProcess P F := by
  intro σ
  obtain ⟨hs,hsm,hst,hsc,hb⟩ := canonical_continuous_localizers P F hF X hm hc hz u hu hut huc
  constructor
  · intro hX n
    exact bounded_local_stop_is_bounded_martingale P F hF hle X hX (σ n) (hs n) (hst n) n (hb n)
  · intro hX
    exact ⟨σ,hs,hsm,hst,hsc,hX⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.min_infimum_eq_of_agree_below
#print axioms Asakura.Chapter2Complete.canonical_continuous_localizers
#print axioms Asakura.Chapter2Complete.local_iff_canonical_bounded_stops
