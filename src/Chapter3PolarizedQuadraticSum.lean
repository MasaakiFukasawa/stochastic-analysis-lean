import Chapter3PolarizedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Polarize the actual infinite sums. Cofinality makes all three sums
finite on the selected prefix, so subtraction of series is justified. -/
theorem partition_cross_sum_polarization
    {ι : Type*} [LinearOrder ι] [OrderTop ι]
    (τ : ℕ → ι) (hτ : Monotone τ)
    (hcofinal : ∀ b, b < ⊤ → ∃ N, b < τ N)
    (X Y : ι → ℝ) (A : ℕ → ℝ) (b t : ι) (hb : b < ⊤) (ht : t ≤ b) :
    (∑' j, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))*
      (Y (min (τ (j+1)) t)-Y (min (τ j) t))) =
    (∑' j, A j*(((1/2:ℝ)*X (min (τ (j+1)) t)+(1/2:ℝ)*Y (min (τ (j+1)) t))-
      ((1/2:ℝ)*X (min (τ j) t)+(1/2:ℝ)*Y (min (τ j) t)))^2)-
    (∑' j, A j*(((1/2:ℝ)*X (min (τ (j+1)) t)+(-1/2:ℝ)*Y (min (τ (j+1)) t))-
      ((1/2:ℝ)*X (min (τ j) t)+(-1/2:ℝ)*Y (min (τ j) t)))^2) := by
  obtain ⟨N,hN⟩ := hcofinal b hb
  have hz (j : ℕ) (hj : j ∉ Finset.range N) (Z : ι → ℝ) :
      Z (min (τ (j+1)) t)-Z (min (τ j) t) = 0 := by
    have hNj := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    have hjt : t ≤ τ j := ht.trans (hN.le.trans (hτ hNj))
    rw [min_eq_right hjt,min_eq_right (hjt.trans (hτ (Nat.le_succ j))),sub_self]
  have hs (Z : ι → ℝ) :
      (∑' j, A j*(Z (min (τ (j+1)) t)-Z (min (τ j) t))^2) =
      ∑ j ∈ Finset.range N, A j*(Z (min (τ (j+1)) t)-Z (min (τ j) t))^2 := by
    apply tsum_eq_sum
    intro j hj
    rw [hz j hj Z,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have hx : (∑' j, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))*
      (Y (min (τ (j+1)) t)-Y (min (τ j) t))) =
      ∑ j ∈ Finset.range N, A j*(X (min (τ (j+1)) t)-X (min (τ j) t))*
      (Y (min (τ (j+1)) t)-Y (min (τ j) t)) := by
    apply tsum_eq_sum
    intro j hj
    rw [hz j hj X,mul_zero,zero_mul]
  rw [hx,hs (fun s => (1/2:ℝ)*X s+(1/2:ℝ)*Y s),
    hs (fun s => (1/2:ℝ)*X s+(-1/2:ℝ)*Y s),← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.partition_cross_sum_polarization
