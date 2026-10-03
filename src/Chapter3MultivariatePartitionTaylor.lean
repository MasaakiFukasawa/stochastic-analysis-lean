import Chapter3FiniteDimensionalTaylor
import Chapter3PartitionTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

noncomputable def partitionLinear {ι : Type*} [LinearOrder ι]
    (X H : ι → ℝ) (τ : ℕ → ι) (t : ι) : ℝ :=
  ∑' j, H (τ j)*(X (min (τ (j+1)) t)-X (min (τ j) t))

/-- Sum the genuine finite-dimensional Taylor remainder along a locally
finite stopping partition. No convergence is assumed here. -/
theorem multivariate_partition_taylor_bound
    {T : EReal} [Fact (0 ≤ T)] {d : ℕ}
    (X : ClosedTime T → (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0 = ⊥)
    (t : ClosedTime T) (N : ℕ) (hN : t ≤ τ N)
    (R ε δ : ℝ)
    (hTaylor : ∀ x ∈ Metric.closedBall 0 R, ∀ y ∈ Metric.closedBall 0 R, ‖y-x‖ ≤ δ →
      |f y-f x-(∑ i, (y i-x i)*fderiv ℝ f x (Pi.single i 1))-
        (∑ i, ∑ k, (y i-x i)*(y k-x k)*
          fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single k 1))/2|
        ≤ (ε/2)*∑ i, (y i-x i)^2)
    (hball : ∀ s, s ≤ t → X s ∈ Metric.closedBall 0 R)
    (hstep : ∀ j, ‖X (min (τ (j+1)) t)-X (min (τ j) t)‖ ≤ δ) :
    |f (X t)-f (X ⊥)-
      (∑ i, partitionLinear (fun s => X s i)
        (fun s => fderiv ℝ f (X s) (Pi.single i 1)) τ t)-
      (∑ i, ∑ k, partitionCross (fun s => X s i) (fun s => X s k)
        (fun s => fderiv ℝ (fderiv ℝ f) (X s) (Pi.single i 1) (Pi.single k 1)) τ t)/2|
    ≤ (ε/2)*∑ i, partitionCross (fun s => X s i) (fun s => X s i) (fun _ => 1) τ t := by
  let dx := fun j i => X (min (τ (j+1)) t) i-X (min (τ j) t) i
  let u := fun j => ∑ i, fderiv ℝ f (X (τ j)) (Pi.single i 1)*dx j i
  let v := fun j => ∑ i, ∑ k, fderiv ℝ (fderiv ℝ f) (X (τ j))
    (Pi.single i 1) (Pi.single k 1)*dx j i*dx j k
  let r := fun j => f (X (min (τ (j+1)) t))-f (X (min (τ j) t))-u j-v j/2
  have hr j : |r j| ≤ (ε/2)*∑ i, (dx j i)^2 := by
    by_cases hj : τ j ≤ t
    · have hh := hTaylor _ (hball _ (min_le_right _ _)) _ (hball _ (min_le_right _ _)) (hstep j)
      rw [min_eq_left hj] at hh
      have hu : (∑ i, (X (min (τ (j+1)) t) i-X (τ j) i)*fderiv ℝ f (X (τ j)) (Pi.single i 1)) = u j := by
        simp only [u,dx,min_eq_left hj,mul_comm]
      have hv : (∑ i, ∑ k, (X (min (τ (j+1)) t) i-X (τ j) i)*(X (min (τ (j+1)) t) k-X (τ j) k)*
          fderiv ℝ (fderiv ℝ f) (X (τ j)) (Pi.single i 1) (Pi.single k 1)) = v j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        dsimp [v,dx]
        rw [min_eq_left hj]
        ring
      rw [hu,hv] at hh
      simpa only [r,dx,min_eq_left hj] using hh
    · have htj := le_of_not_ge hj
      have htj' := htj.trans (hτ (Nat.le_succ j))
      simp [r,u,v,dx,min_eq_right htj,min_eq_right htj']
  have hsum : |∑ j ∈ Finset.range N, r j| ≤ (ε/2)*∑ j ∈ Finset.range N, ∑ i, (dx j i)^2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, |r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, (ε/2)*∑ i, (dx j i)^2 := Finset.sum_le_sum (fun j _ => hr j)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have htel : ∑ j ∈ Finset.range N, (f (X (min (τ (j+1)) t))-f (X (min (τ j) t))) = f (X t)-f (X ⊥) := by
    rw [Finset.sum_range_sub (fun j => f (X (min (τ j) t))),h0,min_eq_right hN,min_bot_left]
  have hu : ∑ j ∈ Finset.range N, u j = ∑ i, partitionLinear (fun s => X s i)
      (fun s => fderiv ℝ f (X s) (Pi.single i 1)) τ t := by
    dsimp only [u,partitionLinear]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact (partition_sum_truncates_before_endpoint τ hτ (fun s => X s i)
      (fun j => fderiv ℝ f (X (τ j)) (Pi.single i 1)) N t hN).symm
  have hv : ∑ j ∈ Finset.range N, v j = ∑ i, ∑ k, partitionCross (fun s => X s i) (fun s => X s k)
      (fun s => fderiv ℝ (fderiv ℝ f) (X s) (Pi.single i 1) (Pi.single k 1)) τ t := by
    dsimp only [v]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact (partition_cross_truncates (fun s => X s i) (fun s => X s k)
      (fun s => fderiv ℝ (fderiv ℝ f) (X s) (Pi.single i 1) (Pi.single k 1)) τ hτ N t hN).symm
  have hq : ∑ j ∈ Finset.range N, ∑ i, (dx j i)^2 =
      ∑ i, partitionCross (fun s => X s i) (fun s => X s i) (fun _ => 1) τ t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [partition_cross_truncates _ _ _ τ hτ N t hN]
    simp only [dx,pow_two,one_mul]
  dsimp only [r] at hsum
  simp only [Finset.sum_sub_distrib] at htel hsum
  rw [htel,hu,← Finset.sum_div,hv,hq] at hsum
  exact hsum

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.multivariate_partition_taylor_bound
