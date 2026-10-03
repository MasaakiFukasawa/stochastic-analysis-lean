import Chapter4C12Taylor
import Chapter3MultivariatePartitionTaylor

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Summation of the separate time/space Taylor remainder. The linear time
errors telescope and only the spatial quadratic variation remains. -/
theorem time_space_partition_taylor_bound
    {T : EReal} [Fact (0≤T)] {dim : ℕ}
    (U : ClosedTime T → ℝ) (X : ClosedTime T → (Fin dim → ℝ))
    (f Dt : ℝ → (Fin dim → ℝ) → ℝ)
    (Dx : Fin dim → ℝ → (Fin dim → ℝ) → ℝ)
    (H : Fin dim → Fin dim → ℝ → (Fin dim → ℝ) → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ) (h0 : τ 0=⊥)
    (t : ClosedTime T) (N : ℕ) (hN : t≤τ N) (ε : ℝ)
    (hTaylor : ∀ j,τ j≤t →
      |f (U (min (τ (j+1)) t)) (X (min (τ (j+1)) t))-f (U (τ j)) (X (τ j))-
        Dt (U (τ j)) (X (τ j))*(U (min (τ (j+1)) t)-U (τ j))-
        (∑ i,(X (min (τ (j+1)) t) i-X (τ j) i)*Dx i (U (τ j)) (X (τ j)))-
        (∑ i,∑ k,(X (min (τ (j+1)) t) i-X (τ j) i)*(X (min (τ (j+1)) t) k-X (τ j) k)*H i k (U (τ j)) (X (τ j)))/2|≤
      ε*(U (min (τ (j+1)) t)-U (τ j))+(ε/2)*∑ i,(X (min (τ (j+1)) t) i-X (τ j) i)^2) :
    |f (U t) (X t)-f (U ⊥) (X ⊥)-partitionLinear U (fun s => Dt (U s) (X s)) τ t-
      (∑ i,partitionLinear (fun s => X s i) (fun s => Dx i (U s) (X s)) τ t)-
      (∑ i,∑ k,partitionCross (fun s => X s i) (fun s => X s k) (fun s => H i k (U s) (X s)) τ t)/2|≤
        ε*(U t-U ⊥)+(ε/2)*∑ i,partitionCross (fun s => X s i) (fun s => X s i) (fun _ => 1) τ t := by
  let dx := fun j i => X (min (τ (j+1)) t) i-X (min (τ j) t) i
  let dt := fun j => U (min (τ (j+1)) t)-U (min (τ j) t)
  let z := fun j => Dt (U (τ j)) (X (τ j))*dt j
  let u := fun j => ∑ i,Dx i (U (τ j)) (X (τ j))*dx j i
  let v := fun j => ∑ i,∑ k,H i k (U (τ j)) (X (τ j))*dx j i*dx j k
  let r := fun j => f (U (min (τ (j+1)) t)) (X (min (τ (j+1)) t))-
    f (U (min (τ j) t)) (X (min (τ j) t))-z j-u j-v j/2
  have hr j : |r j|≤ε*dt j+(ε/2)*∑ i,(dx j i)^2 := by
    by_cases hj : τ j≤t
    · have hh := hTaylor j hj
      have hu : (∑ i,(X (min (τ (j+1)) t) i-X (τ j) i)*Dx i (U (τ j)) (X (τ j)))=u j := by
        simp only [u,dx,min_eq_left hj,mul_comm]
      have hv : (∑ i,∑ k,(X (min (τ (j+1)) t) i-X (τ j) i)*(X (min (τ (j+1)) t) k-X (τ j) k)*H i k (U (τ j)) (X (τ j)))=v j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [v,dx]
        rw [min_eq_left hj]
        ring
      rw [hu,hv] at hh
      simpa only [r,z,dt,dx,min_eq_left hj] using hh
    · have htj := le_of_not_ge hj
      have htj' := htj.trans (hτ (Nat.le_succ j))
      simp [r,z,u,v,dx,dt,min_eq_right htj,min_eq_right htj']
  have hsum : |∑ j∈Finset.range N,r j|≤ε*(∑ j∈Finset.range N,dt j)+
      (ε/2)*∑ j∈Finset.range N,∑ i,(dx j i)^2 := by
    calc
      _ ≤ ∑ j∈Finset.range N,|r j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j∈Finset.range N,(ε*dt j+(ε/2)*∑ i,(dx j i)^2) := Finset.sum_le_sum (fun j _ => hr j)
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  have htel : (∑ j∈Finset.range N,(f (U (min (τ (j+1)) t)) (X (min (τ (j+1)) t))-
      f (U (min (τ j) t)) (X (min (τ j) t))))=f (U t) (X t)-f (U ⊥) (X ⊥) := by
    rw [Finset.sum_range_sub (fun j => f (U (min (τ j) t)) (X (min (τ j) t))),h0,min_eq_right hN,min_bot_left]
  have hdt : (∑ j∈Finset.range N,dt j)=U t-U ⊥ := by
    dsimp only [dt]
    rw [Finset.sum_range_sub (fun j => U (min (τ j) t)),h0,min_eq_right hN,min_bot_left]
  have hz : (∑ j∈Finset.range N,z j)=partitionLinear U (fun s => Dt (U s) (X s)) τ t := by
    exact (partition_sum_truncates_before_endpoint τ hτ U (fun j => Dt (U (τ j)) (X (τ j))) N t hN).symm
  have hu : (∑ j∈Finset.range N,u j)=∑ i,partitionLinear (fun s => X s i) (fun s => Dx i (U s) (X s)) τ t := by
    dsimp only [u,partitionLinear]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact (partition_sum_truncates_before_endpoint τ hτ (fun s => X s i) (fun j => Dx i (U (τ j)) (X (τ j))) N t hN).symm
  have hv : (∑ j∈Finset.range N,v j)=∑ i,∑ k,partitionCross (fun s => X s i) (fun s => X s k) (fun s => H i k (U s) (X s)) τ t := by
    dsimp only [v]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact (partition_cross_truncates (fun s => X s i) (fun s => X s k) (fun s => H i k (U s) (X s)) τ hτ N t hN).symm
  have hq : (∑ j∈Finset.range N,∑ i,(dx j i)^2)=∑ i,partitionCross (fun s => X s i) (fun s => X s i) (fun _ => 1) τ t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [partition_cross_truncates _ _ _ τ hτ N t hN]
    simp only [dx,pow_two,one_mul]
  dsimp only [r] at hsum
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,htel,hz,hu,←Finset.sum_div,hv,hdt,hq] at hsum
  exact hsum

end Asakura.Chapter4
