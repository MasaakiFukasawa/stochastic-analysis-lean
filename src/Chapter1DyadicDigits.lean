import FullAuditPartitionExercise
import Mathlib.Algebra.Order.Floor.Ring

open Set
open scoped BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 3000000

noncomputable def dyadicFloor (n : ℕ) (x : ℝ) : ℤ := ⌊(2:ℝ)^n*x⌋
noncomputable def dyadicDigit (n : ℕ) (x : ℝ) : ℤ := dyadicFloor (n+1) x % 2
noncomputable def dyadicCode (n : ℕ) (x : ℝ) : ℤ := dyadicFloor n x-(2:ℤ)^n*⌊x⌋

lemma dyadic_floor_half (n : ℕ) (x : ℝ) : dyadicFloor (n+1) x/2=dyadicFloor n x := by
  have h := Int.mul_natCast_floor_div_cancel (n := 2) (by norm_num) ((2:ℝ)^n*x)
  simpa only [dyadicFloor,pow_succ,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using h

lemma dyadic_digit_bounds (n : ℕ) (x : ℝ) : 0≤dyadicDigit n x ∧ dyadicDigit n x<2 :=
  ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩

lemma dyadic_floor_rec (n : ℕ) (x : ℝ) :
    dyadicFloor (n+1) x=2*dyadicFloor n x+dyadicDigit n x := by
  have h := dyadic_floor_half n x
  dsimp only [dyadicDigit]
  omega

lemma dyadic_code_zero (x : ℝ) : dyadicCode 0 x=0 := by simp [dyadicCode,dyadicFloor]

lemma dyadic_code_rec (n : ℕ) (x : ℝ) :
    dyadicCode (n+1) x=2*dyadicCode n x+dyadicDigit n x := by
  dsimp only [dyadicCode]
  rw [dyadic_floor_rec,pow_succ]
  ring

lemma dyadic_code_bounds (n : ℕ) (x : ℝ) : 0≤dyadicCode n x ∧ dyadicCode n x<(2:ℤ)^n := by
  induction n with
  | zero => simp [dyadic_code_zero]
  | succ n ih =>
    rw [dyadic_code_rec,pow_succ]
    have hd := dyadic_digit_bounds n x
    constructor <;> omega

/-- The first n binary digits and their single dyadic cell index have
exactly the same fibers, including all endpoints. -/
theorem dyadic_prefix_fibers (n : ℕ) (x y : ℝ) :
    (∀ i<n,dyadicDigit i x=dyadicDigit i y) ↔ dyadicCode n x=dyadicCode n y := by
  induction n with
  | zero => simp [dyadic_code_zero]
  | succ n ih =>
    constructor
    · intro h
      rw [dyadic_code_rec,dyadic_code_rec,ih.mp (fun i hi => h i (by omega)),h n (by omega)]
    · intro h
      rw [dyadic_code_rec,dyadic_code_rec] at h
      have hx := dyadic_digit_bounds n x
      have hy := dyadic_digit_bounds n y
      have hc : dyadicCode n x=dyadicCode n y := by omega
      have hd : dyadicDigit n x=dyadicDigit n y := by omega
      intro i hi
      by_cases he : i=n
      · simpa only [he] using hd
      · exact ih.mpr hc i (by omega)

/-- The printed weighted digit sum is exactly the left cell endpoint.
For x=1 it is zero, correctly retaining the exceptional endpoint's fiber. -/
theorem dyadic_weighted_digits (n : ℕ) (x : ℝ) :
    (∑ i∈Finset.range n,(dyadicDigit i x:ℝ)/(2:ℝ)^(i+1))=(dyadicCode n x:ℝ)/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadic_code_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,dyadic_code_rec]
    push_cast
    rw [pow_succ]
    field_simp

lemma dyadic_code_on_unit_interval (n : ℕ) (x : ℝ) (hx : x∈Ico (0:ℝ) 1) :
    dyadicCode n x=dyadicFloor n x := by
  have hz : ⌊x⌋=(0:ℤ) := by rw [Int.floor_eq_iff]; simpa using hx
  simp [dyadicCode,hz]

end Asakura.Chapter1Complete
