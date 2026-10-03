import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators
namespace Asakura.Chapter6

/-- The endpoint singularity in the bridge estimate is summable. -/
theorem inverse_sqrt_sum (n : ℕ) :
    ∑ k ∈ range n, 1 / Real.sqrt ((k:ℝ)+1) ≤ 2*Real.sqrt (n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    have hp : 0<Real.sqrt ((n:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
    have hm : Real.sqrt (n:ℝ)≤Real.sqrt ((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
    have hs := Real.sq_sqrt hn
    have ht := Real.sq_sqrt (show 0≤(n:ℝ)+1 by positivity)
    have hstep : 1/Real.sqrt ((n:ℝ)+1)≤2*(Real.sqrt ((n:ℝ)+1)-Real.sqrt (n:ℝ)) := by
      apply (div_le_iff₀ hp).2
      nlinarith [sq_nonneg (Real.sqrt ((n:ℝ)+1)-Real.sqrt (n:ℝ))]
    push_cast
    linarith

theorem bridge_grid_singular_sum (n : ℕ) (h : ℝ) (hh : 0<h) :
    ∑ k ∈ range n, h/Real.sqrt ((n:ℝ)*h-(k:ℝ)*h) ≤ 2*Real.sqrt ((n:ℝ)*h) := by
  have he : (∑ k ∈ range n, h/Real.sqrt ((n:ℝ)*h-(k:ℝ)*h)) =
      Real.sqrt h * ∑ k ∈ range n, 1/Real.sqrt ((k:ℝ)+1) := by
    rw [←sum_range_reflect (fun k => h/Real.sqrt ((n:ℝ)*h-(k:ℝ)*h)) n,mul_sum]
    apply sum_congr rfl
    intro k hk
    have hk' : k<n := mem_range.mp hk
    have hcast : ((n-1-k:ℕ):ℝ)=(n:ℝ)-1-k := by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
      norm_num
    rw [hcast,show (n:ℝ)*h-((n:ℝ)-1-k)*h=((k:ℝ)+1)*h by ring,
      Real.sqrt_mul (by positivity)]
    have hs := Real.sq_sqrt hh.le
    have hp : 0<Real.sqrt h := Real.sqrt_pos.2 hh
    have hkpos : 0<Real.sqrt ((k:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
    field_simp
    nlinarith
  rw [he]
  have hb := mul_le_mul_of_nonneg_left (inverse_sqrt_sum n) (Real.sqrt_nonneg h)
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  nlinarith

end Asakura.Chapter6
