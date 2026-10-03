import Chapter3PartitionStepRegularity
import Chapter2LocalizedApproximation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Before the Nth endpoint the countable discrete sum is exactly its
first N terms. This includes equality at the endpoint. -/
theorem partition_sum_truncates_before_endpoint
    {ι : Type*} [LinearOrder ι] (τ : ℕ → ι) (hτ : Monotone τ)
    (X : ι → ℝ) (A : ℕ → ℝ) (N : ℕ) (t : ι) (ht : t ≤ τ N) :
    (∑' j, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))) =
      ∑ j ∈ Finset.range N, A j*(X (min (τ (j+1)) t)-X (min (τ j) t)) := by
  apply tsum_eq_sum
  intro j hj
  have hNj := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  have hjt := ht.trans (hτ hNj)
  rw [min_eq_right hjt,min_eq_right (hjt.trans (hτ (Nat.le_succ j))),sub_self,mul_zero]

/-- Truncating the actual discrete integral converges in probability
uniformly on a finite prefix. The exceptional event is explicitly bounded
by the probability that the Nth stopping time precedes that prefix. -/
theorem discrete_sum_truncation_probability
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτm : ∀ ω, Monotone (fun j => τ j ω))
    (hτc : ∀ ω t, t < ⊤ → ∃ j, t < τ j ω)
    (X : ClosedTime T → Ω → ℝ) (A : ℕ → Ω → ℝ)
    (b : ClosedTime T) (hb : b < ⊤) (ε : ℝ) (hε : 0 < ε) :
    let R := fun t ω => ∑' j, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)
    let Rn := fun n t ω => ∑ j ∈ Finset.range n, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)
    Tendsto (fun n => P {ω | ε ≤ ⨆ s, |Rn n (min b s) ω-R (min b s) ω|}) atTop (𝓝 0) ∧
    Tendsto (fun n => P {ω | ε ≤ |Rn n b ω-R b ω|}) atTop (𝓝 0) := by
  intro R Rn
  have hp := cofinal_stopping_probability_limit P τ b
    (fun n => hle b _ (strict_stopping_event_measurable F hF (τ n) (hτ n) b)) hτm
    (fun ω => (hτc ω b hb).imp (fun _ h => h.le))
  have he (n ω) (hω : ¬ τ n ω < b) (s) (hs : s ≤ b) : Rn n s ω = R s ω :=
    (partition_sum_truncates_before_endpoint (fun j => τ j ω) (hτm ω) (fun t => X t ω)
      (fun j => A j ω) n s (hs.trans (le_of_not_gt hω))).symm
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp (fun _ => bot_le)
    intro n
    apply measure_mono
    intro ω hω
    by_contra hn
    have hz : (⨆ s, |Rn n (min b s) ω-R (min b s) ω|) = 0 := by
      simp only [he n ω hn _ (min_le_left _ _),sub_self,abs_zero,ciSup_const]
    change ε ≤ _ at hω
    rw [hz] at hω
    exact not_le_of_gt hε hω
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp (fun _ => bot_le)
    intro n
    apply measure_mono
    intro ω hω
    by_contra hn
    change ε ≤ _ at hω
    rw [he n ω hn b le_rfl,sub_self,abs_zero] at hω
    exact not_le_of_gt hε hω

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_sum_truncates_before_endpoint
#print axioms Asakura.Chapter3Complete.discrete_sum_truncation_probability
