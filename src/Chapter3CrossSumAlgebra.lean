import Chapter3VariationPartitionBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def partitionCross {ι : Type*} [LinearOrder ι]
    (X Y H : ι → ℝ) (τ : ℕ → ι) (t : ι) : ℝ :=
  ∑' j, H (τ j)*(X (min (τ (j+1)) t)-X (min (τ j) t))*(Y (min (τ (j+1)) t)-Y (min (τ j) t))

theorem partition_cross_truncates
    {ι : Type*} [LinearOrder ι] (X Y H : ι → ℝ) (τ : ℕ → ι) (hτ : Monotone τ)
    (N : ℕ) (t : ι) (ht : t ≤ τ N) :
    partitionCross X Y H τ t = ∑ j ∈ Finset.range N,
      H (τ j)*(X (min (τ (j+1)) t)-X (min (τ j) t))*(Y (min (τ (j+1)) t)-Y (min (τ j) t)) := by
  apply tsum_eq_sum
  intro j hj
  have hNj : N ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  have htj := ht.trans (hτ hNj)
  rw [min_eq_right htj,min_eq_right (htj.trans (hτ (Nat.le_succ j))),sub_self,mul_zero,zero_mul]

/-- The exact weighted Cauchy-Schwarz inequality printed in prop:qcv2,
for the actual countable locally finite sums. -/
theorem partition_cross_cauchy_schwarz
    {T : EReal} [Fact (0 ≤ T)] (A M H : ClosedTime T → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (hco : ∀ t, t < ⊤ → ∃ N, t < τ N) (t : ClosedTime T) (ht : t < ⊤) :
    (partitionCross A M H τ t)^2 ≤
      partitionCross A A (fun s => |H s|) τ t * partitionCross M M (fun s => |H s|) τ t := by
  obtain ⟨N,hN⟩ := hco t ht
  rw [partition_cross_truncates A M H τ hτ N t hN.le,
    partition_cross_truncates A A (fun s => |H s|) τ hτ N t hN.le,
    partition_cross_truncates M M (fun s => |H s|) τ hτ N t hN.le]
  simpa only [pow_two,mul_assoc] using Asakura.Chapter3Written.weighted_mixed_cauchy_schwarz
    (Finset.range N) (fun j => H (τ j))
    (fun j => A (min (τ (j+1)) t)-A (min (τ j) t))
    (fun j => M (min (τ (j+1)) t)-M (min (τ j) t))

/-- The four-term semimartingale expansion, derived for actual infinite
sums and using component equality only on the finite prefix. -/
theorem partition_cross_decomposition
    {T : EReal} [Fact (0 ≤ T)] (X Y A B M N H : ClosedTime T → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (hco : ∀ t, t < ⊤ → ∃ J, t < τ J) (b : ClosedTime T) (hb : b < ⊤)
    (hX : ∀ s, s ≤ b → X s = A s+M s) (hY : ∀ s, s ≤ b → Y s = B s+N s)
    (t : ClosedTime T) :
    partitionCross X Y H τ (min b t) =
      partitionCross A B H τ (min b t)+partitionCross A N H τ (min b t)+
      partitionCross B M H τ (min b t)+partitionCross M N H τ (min b t) := by
  obtain ⟨J,hJ⟩ := hco b hb
  have hj := (min_le_left b t).trans hJ.le
  rw [partition_cross_truncates X Y H τ hτ J _ hj,
    partition_cross_truncates A B H τ hτ J _ hj,
    partition_cross_truncates A N H τ hτ J _ hj,
    partition_cross_truncates B M H τ hτ J _ hj,
    partition_cross_truncates M N H τ hτ J _ hj]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hX _ ((min_le_right _ _).trans (min_le_left _ _)),hX _ ((min_le_right _ _).trans (min_le_left _ _)),
    hY _ ((min_le_right _ _).trans (min_le_left _ _)),hY _ ((min_le_right _ _).trans (min_le_left _ _))]
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_cross_truncates
#print axioms Asakura.Chapter3Complete.partition_cross_cauchy_schwarz
#print axioms Asakura.Chapter3Complete.partition_cross_decomposition
