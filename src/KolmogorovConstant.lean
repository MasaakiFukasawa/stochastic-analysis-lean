import KolmogorovCommon
open scoped ENNReal
namespace Asakura

/-- Algebraic normalization of the geometric-series denominator. -/
theorem kolmogorov_constant_identity (c A α ε : ℝ) (hαε : α < ε) :
    (2 * (2:ℝ)^α) * ((c*A) / (1 - 2^α * 2^(-ε))) =
      2*c*A / (2^(-α) - 2^(-ε)) := by
  have hq : (0:ℝ) < 2^α := Real.rpow_pos_of_pos (by norm_num) _
  have hr : (2:ℝ)^α * 2^(-ε) < 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have heq : (2:ℝ)^α * (2^(-α)-2^(-ε)) = 1 - 2^α*2^(-ε) := by
    rw [mul_sub, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    simp
  have hd : 0 < (2:ℝ)^(-α)-2^(-ε) := by nlinarith
  rw [← heq]
  field_simp
  <;> ring

/-- The manuscript's printed constant dominates the sharper maximum-norm bound. -/
theorem kolmogorov_printed_constant (d : ℕ) (hd : 1 ≤ d)
    (p c ε α : ℝ) (hp : 0 < p) (hc : 0 ≤ c) (hε : 0 < ε) (hαε : α < ε) :
    (2 * (2:ℝ)^α) * ((c * (6:ℝ)^(d/p)) / (1 - 2^α * 2^(-ε))) ≤
      (2*c / (2^(-α)-2^(-ε))) * (6 * Real.sqrt d)^(ε+d/p) := by
  rw [kolmogorov_constant_identity c ((6:ℝ)^(d/p)) α ε hαε]
  have hdReal : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : 1 ≤ Real.sqrt (d:ℝ) := by
    have hh := Real.sqrt_le_sqrt hdReal
    simpa using hh
  have hpow : (6:ℝ)^(d/p) ≤ (6 * Real.sqrt d)^(ε+d/p) := by
    calc
      (6:ℝ)^(d/p) ≤ 6^(ε+d/p) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ (6 * Real.sqrt d)^(ε+d/p) :=
        Real.rpow_le_rpow (by norm_num) (by linarith) (by positivity)
  have hden : 0 < (2:ℝ)^(-α)-2^(-ε) := by
    apply sub_pos.mpr
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hcoef : 0 ≤ 2*c / ((2:ℝ)^(-α)-2^(-ε)) := by positivity
  convert mul_le_mul_of_nonneg_left hpow hcoef using 1 <;> ring
end Asakura
