import FullAuditChapter5Estimates

namespace Asakura.Chapter5

/-- The two Young inequalities in the printed energy argument, including C=0. -/
theorem young_generator_bound (C l m y z d : ℝ)
    (hC : 0 ≤ C) (hl : 0 < l) (hm : 0 < m) :
    2 * |y| * (C * (|y| + |z|) + |d|) ≤
      (2*C+C*l+m)*y^2 + C/l*z^2 + d^2/m := by
  have young (a b k : ℝ) (hk : 0 < k) :
      2 * |a| * |b| ≤ k*a^2+b^2/k := by
    have he : k*a^2+b^2/k-2 * |a| * |b| = (k*|a|-|b|)^2/k := by
      rw [sub_sq, mul_pow, sq_abs, sq_abs]
      field_simp
      <;> ring
    have hn := div_nonneg (sq_nonneg (k*|a|-|b|)) hk.le
    rw [← he] at hn
    linarith
  calc
    2 * |y| * (C * (|y| + |z|) + |d|) =
        2*C*|y|^2 + C*(2 * |y| * |z|) + 2 * |y| * |d| := by ring
    _ ≤ 2*C*|y|^2 + C*(l*y^2+z^2/l) + (m*y^2+d^2/m) :=
      add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left (young y z l hl) hC) _)
        (young y d m hm)
    _ = (2*C+C*l+m)*y^2 + C/l*z^2 + d^2/m := by rw [sq_abs]; ring

/-- Absorption in the weighted energy identity. A,B are the remaining
weighted integrals and U the squared value at time t. This is only the
algebraic part; the stochastic energy identity is not an assumption-free input. -/
theorem absorb_energy (C l m beta U A B R D : ℝ)
    (hC : 0 ≤ C) (hl : C < l) (hm : 0 < m)
    (hb : C*(2+l)+m ≤ beta) (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : U+beta*A+B ≤ R+(2*C+C*l+m)*A+(C/l)*B+D/m) :
    U ≤ R+D/m ∧ B ≤ l/(l-C)*(R+D/m) := by
  have hl0 : 0 < l := lt_of_le_of_lt hC hl
  have hcoef : 0 < 1-C/l := by apply sub_pos.mpr; exact (div_lt_one hl0).2 hl
  have hbeta : 0 ≤ (beta-(2*C+C*l+m))*A :=
    mul_nonneg (by nlinarith) hA
  have hBcoef : 0 ≤ (1-C/l)*B := mul_nonneg hcoef.le hB
  constructor
  · nlinarith
  · have h : (1-C/l)*B ≤ R+D/m := by nlinarith
    have heq : 1-C/l = (l-C)/l := by field_simp
    rw [heq] at h
    have h' : (l-C)*B ≤ (R+D/m)*l := by
      apply (div_le_iff₀ hl0).1
      simpa [div_mul_eq_mul_div] using h
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sub_pos.mpr hl)).2
    nlinarith


/-- The square of the contraction constant is strictly below one. -/
theorem contraction_ratio (T C beta : ℝ) (hT : 0 ≤ T)
    (hb : 2*(1+T)*C^2 < beta) :
    0 ≤ 2*(1+T)*C^2/beta ∧ 2*(1+T)*C^2/beta < 1 := by
  have hn : 0 ≤ 2*(1+T)*C^2 := by positivity
  have hp : 0 < beta := lt_of_le_of_lt hn hb
  exact ⟨div_nonneg hn hp.le, (div_lt_one hp).2 hb⟩

/-- Frozen generators have Lipschitz constant zero; the positive-C statement
in the manuscript must explicitly allow this boundary case. -/
theorem frozen_generator_lipschitz_zero (g : ℝ) (y z y' z' : ℝ) :
    |g-g| ≤ 0*(|y-y'|+|z-z'|) := by simp

end Asakura.Chapter5
