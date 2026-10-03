import Chapter3OscillationPartition

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Capping an infimum only uses the set below the cap. -/
theorem capped_inf_eq_of_agree_below
    {ι : Type*} [CompleteLinearOrder ι] (A B : Set ι) (c : ι)
    (h : ∀ t, t ≤ c → (t ∈ A ↔ t ∈ B)) :
    min (sInf A) c = min (sInf B) c := by
  have hh (A B : Set ι) (h : ∀ t, t ≤ c → (t ∈ A ↔ t ∈ B)) :
      min (sInf A) c ≤ min (sInf B) c := by
    refine le_min (le_sInf ?_) (min_le_right _ _)
    intro t ht
    by_cases htc : t ≤ c
    · exact (min_le_left _ _).trans (sInf_le ((h t htc).mpr ht))
    · exact (min_le_right _ _).trans (le_of_not_ge htc)
  exact le_antisymm (hh A B h) (hh B A (fun t ht => (h t ht).symm))

/-- The constructed stopping partition obeys exactly the uncapped hitting
formula printed in the manuscript, despite the auxiliary cap in its Lean
definition. No continuity of X at T is used for this identification. -/
theorem oscillation_partition_original_formula
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ) (c : ℕ → ClosedTime T) (δ : ℝ) (n : ℕ) (ω : Ω) :
    oscillationPartition X c δ (n+1) ω =
      min (sInf {s | δ ≤ |X s ω-X (min (oscillationPartition X c δ n ω) s) ω|}) (c n) := by
  change min (sInf {s | δ ≤ |X (min (c n) s) ω-
      X (min (c n) (min (oscillationPartition X c δ n ω) s)) ω|}) (c n) = _
  apply capped_inf_eq_of_agree_below
  intro t ht
  change (δ ≤ |X (min (c n) t) ω-X (min (c n) (min (oscillationPartition X c δ n ω) t)) ω|) ↔
    (δ ≤ |X t ω-X (min (oscillationPartition X c δ n ω) t) ω|)
  simp only [min_eq_right ht,min_eq_right ((min_le_right _ _).trans ht)]

/-- The all-time increment condition gives the interval oscillation
condition used for the Stieltjes approximation. -/
theorem interval_oscillation_of_stopped_increments
    {ι : Type*} [LinearOrder ι] (X : ι → ℝ) (τ : ℕ → ι) (δ : ℝ)
    (hb : ∀ j t, |X (min (τ (j+1)) t)-X (min (τ j) t)| ≤ δ) :
    ∀ j t, τ j ≤ t → t ≤ τ (j+1) → |X (τ j)-X t| ≤ δ := by
  intro j t hj ht
  simpa only [min_eq_right ht,min_eq_left hj,abs_sub_comm] using hb j t

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.capped_inf_eq_of_agree_below
#print axioms Asakura.Chapter3Complete.oscillation_partition_original_formula
#print axioms Asakura.Chapter3Complete.interval_oscillation_of_stopped_increments
