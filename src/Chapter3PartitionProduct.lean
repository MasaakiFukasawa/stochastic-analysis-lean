import Chapter3MultivariatePartitionTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The exact degree-two Taylor identity underlying integration by parts. -/
theorem partition_product_identity
    {T : EReal} [Fact (0 ≤ T)] (X Y : ClosedTime T → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (t : ClosedTime T) (N : ℕ) (hN : t ≤ τ N) :
    X t*Y t-X ⊥*Y ⊥ = partitionLinear X Y τ t+partitionLinear Y X τ t+
      partitionCross X Y (fun _ => 1) τ t := by
  rw [partitionLinear,partitionLinear,
    partition_sum_truncates_before_endpoint τ hτ X (fun j => Y (τ j)) N t hN,
    partition_sum_truncates_before_endpoint τ hτ Y (fun j => X (τ j)) N t hN,
    partition_cross_truncates X Y (fun _ => 1) τ hτ N t hN,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  have he j : Y (τ j)*(X (min (τ (j+1)) t)-X (min (τ j) t))+
      X (τ j)*(Y (min (τ (j+1)) t)-Y (min (τ j) t))+
      1*(X (min (τ (j+1)) t)-X (min (τ j) t))*(Y (min (τ (j+1)) t)-Y (min (τ j) t)) =
      X (min (τ (j+1)) t)*Y (min (τ (j+1)) t)-X (min (τ j) t)*Y (min (τ j) t) := by
    by_cases hj : τ j ≤ t
    · rw [min_eq_left hj]; ring
    · have hta := le_of_not_ge hj
      simp [min_eq_right hta,min_eq_right (hta.trans (hτ (Nat.le_succ j)))]
  simp_rw [he]
  rw [Finset.sum_range_sub (fun j => X (min (τ j) t)*Y (min (τ j) t)),
    h0,min_eq_right hN,min_bot_left]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_product_identity
