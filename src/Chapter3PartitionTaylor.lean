import Chapter3CrossSumAlgebra
import Chapter3WrittenTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Taylor's intermediate point is on the continuous time path. The case
where the left endpoint is already beyond t has zero increment. -/
theorem stopped_partition_taylor_increment
    {T : EReal} [Fact (0 ≤ T)] (X : ClosedTime T → ℝ)
    (hX : ∀ t, t < ⊤ → ContinuousAt X t)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (a b t : ClosedTime T) (hab : a ≤ b) (hbt : b < ⊤)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ s, ‖iteratedDeriv 2 f (X (min b s))-
      iteratedDeriv 2 f (X (min a s))‖ ≤ δ) :
    |f (X (min b t))-f (X (min a t))-
      deriv f (X a)*(X (min b t)-X (min a t))-
      iteratedDeriv 2 f (X a)*(X (min b t)-X (min a t))^2/2|
      ≤ δ*(X (min b t)-X (min a t))^2/2 := by
  by_cases hat : a ≤ t
  · have ham : a ≤ min b t := le_min hab hat
    have hc : ContinuousOn X (uIcc a (min b t)) := by
      rw [uIcc_of_le ham]
      intro s hs
      exact (hX s (hs.2.trans_lt ((min_le_left _ _).trans_lt hbt))).continuousWithinAt
    have hs : ∀ z ∈ uIcc (X a) (X (min b t)),
        |iteratedDeriv 2 f z-iteratedDeriv 2 f (X a)| ≤ δ := by
      intro z hz
      obtain ⟨s,hs,rfl⟩ := intermediate_value_uIcc hc hz
      rw [uIcc_of_le ham] at hs
      have hh := hosc s
      simpa only [min_eq_left hs.1,min_eq_right (hs.2.trans (min_le_left _ _)),
        Real.norm_eq_abs] using hh
    simpa only [min_eq_left hat] using
      Asakura.Chapter3Written.taylor_second_order_oscillation hf hδ hs
  · have hta : t ≤ a := le_of_not_ge hat
    simp only [min_eq_right hta,min_eq_right (hta.trans hab),sub_self,mul_zero,
      zero_pow (by norm_num : 2 ≠ 0),zero_div,abs_zero,le_refl]

/-- The literal locally finite Taylor sum in the scalar Ito proof. -/
theorem stopped_partition_taylor_sum
    {T : EReal} [Fact (0 ≤ T)] (X : ClosedTime T → ℝ)
    (hX : ∀ t, t < ⊤ → ContinuousAt X t)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (hfin : ∀ j, τ j < ⊤) (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j s, ‖iteratedDeriv 2 f (X (min (τ (j+1)) s))-
      iteratedDeriv 2 f (X (min (τ j) s))‖ ≤ δ)
    (t : ClosedTime T) (ht : t < ⊤) :
    |f (X t)-f (X ⊥)-
      (∑' j, deriv f (X (τ j))*(X (min (τ (j+1)) t)-X (min (τ j) t)))-
      partitionCross X X (fun s => iteratedDeriv 2 f (X s)) τ t/2|
      ≤ (δ/2)*partitionCross X X (fun _ => 1) τ t := by
  obtain ⟨N,hN⟩ := hco t ht
  rw [partition_sum_truncates_before_endpoint τ hτ X (fun j => deriv f (X (τ j))) N t hN.le,
    partition_cross_truncates X X (fun s => iteratedDeriv 2 f (X s)) τ hτ N t hN.le,
    partition_cross_truncates X X (fun _ => 1) τ hτ N t hN.le]
  let dx := fun j => X (min (τ (j+1)) t)-X (min (τ j) t)
  let r := fun j => f (X (min (τ (j+1)) t))-f (X (min (τ j) t))-
    deriv f (X (τ j))*dx j-iteratedDeriv 2 f (X (τ j))*(dx j)^2/2
  have hr : ∀ j ∈ Finset.range N, |r j| ≤ (δ/2)*(dx j)^2 := by
    intro j _
    have hh := stopped_partition_taylor_increment X hX f hf (τ j) (τ (j+1)) t
      (hτ (Nat.le_succ j)) (hfin (j+1)) δ hδ (hosc j)
    dsimp [r,dx]
    nlinarith [hh]
  have he : ∑ j ∈ Finset.range N, (f (X (min (τ (j+1)) t))-f (X (min (τ j) t))) =
      f (X t)-f (X ⊥) := by
    rw [Finset.sum_range_sub (fun j => f (X (min (τ j) t))),h0,
      min_eq_right hN.le,min_bot_left]
  have hh := Asakura.Chapter3Written.sum_remainder_bound (Finset.range N) r dx (δ/2) hr
  dsimp [r] at hh
  simp only [Finset.sum_sub_distrib,Finset.sum_div] at hh
  simp only [Finset.sum_sub_distrib] at he
  rw [he,← Finset.sum_div] at hh
  simpa only [dx,pow_two,mul_assoc,one_mul] using hh

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_partition_taylor_increment
#print axioms Asakura.Chapter3Complete.stopped_partition_taylor_sum
