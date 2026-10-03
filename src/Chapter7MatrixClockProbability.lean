import Chapter7BrownianClockProbability
import Chapter7FiniteEnergySum

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The matrix clock is a finite sum of projected-square clocks. -/
theorem matrix_cell_clock_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (K : Fin d → Fin d → ℝ) (T t : ℝ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) :
    TendstoInMeasure P (fun n w => ∑ i,brownianCellClock B (K i) T t (n+1) w) atTop
      (fun _ => (2*(∑ i,∑ j,(K i j)^2)/T)*t) := by
  let q := fun i => ∑ j,(K i j)^2
  let c := fun i => (2*q i/T)*t
  let X := fun n i w => brownianCellClock B (K i) T t (n+1) w-c i
  have hi n i : MemLp (X n i) 2 P :=
    (brownian_cell_clock_mean P B (K i) T t (n+1) hT ht0 htT (Nat.succ_pos _)).1.sub (memLp_const _)
  have hc : (∑ i,c i)=(2*(∑ i,q i)/T)*t := by
    dsimp only [c]
    rw [← sum_mul,← sum_div,← mul_sum]
  have he n w : (∑ i,brownianCellClock B (K i) T t (n+1) w)-(2*(∑ i,q i)/T)*t=∑ i,X n i w := by
    simp only [X,sum_sub_distrib,hc]
  apply mean_square_rate_probability P _ _ ((d:ℝ)*32*(∑ i,(q i)^2)) ((d:ℝ)*4*(∑ i,(q i)^2))
  · intro n
    simpa only [← he] using memLp_finsetSum univ (fun i _ => hi n i)
  · intro n
    change (∫ w,((∑ i,brownianCellClock B (K i) T t (n+1) w)-(2*(∑ i,q i)/T)*t)^2 ∂P) ≤ _
    simp only [he]
    have hb := finite_energy_sum P (X n) (hi n)
    have hsum : (∑ i,∫ w,(X n i w)^2 ∂P) ≤
      ∑ i,(32*(q i)^2/((n:ℝ)+1)+4*(q i)^2/((n:ℝ)+1)^2) := by
      apply sum_le_sum
      intro i _
      exact brownian_cell_clock_error_bound P B (K i) T t hT ht0 htT n
    apply hb.trans
    apply (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)).trans_eq
    simp only [sum_add_distrib,← sum_div,← mul_sum]
    ring

end Asakura.Chapter7
