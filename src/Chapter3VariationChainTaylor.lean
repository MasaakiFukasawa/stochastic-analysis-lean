import Chapter3PartitionTaylor
import Chapter3VariationCrossConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem first_order_taylor_oscillation {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {x y δ : ℝ} (hosc : ∀ z ∈ uIcc x y, |deriv f z-deriv f x| ≤ δ) :
    |f y-f x-deriv f x*(y-x)| ≤ δ*|y-x| := by
  by_cases hxy : x=y
  · subst y; simp
  obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 0) hxy hf.contDiffOn
  simp only [taylor_within_zero_eval,iteratedDeriv_one] at he
  norm_num at he
  have hr : f y-f x-deriv f x*(y-x) = (deriv f z-deriv f x)*(y-x) := by nlinarith [he]
  rw [hr,abs_mul]
  exact mul_le_mul_of_nonneg_right (hosc z ⟨hz.1.le,hz.2.le⟩) (abs_nonneg _)

/-- First-order chain-rule remainder controlled by actual total variation. -/
theorem variation_chain_partition_bound
    {T : EReal} [Fact (0 ≤ T)] (A : ClosedTime T → ℝ)
    (hA : ∀ t, t < ⊤ → ContinuousAt A t)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j s, ‖deriv f (A (min (τ (j+1)) s))-deriv f (A (min (τ j) s))‖ ≤ δ)
    (t : ClosedTime T) (ht : t < ⊤) (hBV : BoundedVariationOn A (Iic t)) :
    |f (A t)-f (A ⊥)-∑' j, deriv f (A (τ j))*(A (min (τ (j+1)) t)-A (min (τ j) t))|
      ≤ δ*(eVariationOn A (Iic t)).toReal := by
  obtain ⟨N,hN⟩ := hco t ht
  rw [partition_sum_truncates_before_endpoint τ hτ A (fun j => deriv f (A (τ j))) N t hN.le]
  let dx := fun j => A (min (τ (j+1)) t)-A (min (τ j) t)
  let r := fun j => f (A (min (τ (j+1)) t))-f (A (min (τ j) t))-deriv f (A (τ j))*dx j
  have hr j : |r j| ≤ δ*|dx j| := by
    by_cases hj : τ j ≤ t
    · have ham : τ j ≤ min (τ (j+1)) t := le_min (hτ (Nat.le_succ j)) hj
      have hc : ContinuousOn A (uIcc (τ j) (min (τ (j+1)) t)) := by
        rw [uIcc_of_le ham]
        intro s hs
        exact (hA s ((hs.2.trans (min_le_right _ _)).trans_lt ht)).continuousWithinAt
      have hs : ∀ z ∈ uIcc (A (τ j)) (A (min (τ (j+1)) t)),
          |deriv f z-deriv f (A (τ j))| ≤ δ := by
        intro z hz
        obtain ⟨s,hs,rfl⟩ := intermediate_value_uIcc hc hz
        rw [uIcc_of_le ham] at hs
        simpa only [min_eq_left hs.1,min_eq_right (hs.2.trans (min_le_left _ _)),Real.norm_eq_abs]
          using hosc j s
      simpa only [r,dx,min_eq_left hj] using first_order_taylor_oscillation hf hs
    · have hta := le_of_not_ge hj
      simp [r,dx,min_eq_right hta,min_eq_right (hta.trans (hτ (Nat.le_succ j)))]
  have hsum : |∑ j ∈ Finset.range N, r j| ≤ δ*∑ j ∈ Finset.range N, |dx j| := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, |r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, δ*|dx j| := Finset.sum_le_sum (fun j _ => hr j)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have htel : ∑ j ∈ Finset.range N, (f (A (min (τ (j+1)) t))-f (A (min (τ j) t))) = f (A t)-f (A ⊥) := by
    rw [Finset.sum_range_sub (fun j => f (A (min (τ j) t))),h0,min_eq_right hN.le,min_bot_left]
  dsimp only [r] at hsum
  simp only [Finset.sum_sub_distrib] at htel hsum
  rw [htel] at hsum
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left _ hδ
  simpa only [min_self,dx] using stopped_partition_variation_bound A t hBV τ hτ t N

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.first_order_taylor_oscillation
#print axioms Asakura.Chapter3Complete.variation_chain_partition_bound
