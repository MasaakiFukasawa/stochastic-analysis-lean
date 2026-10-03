import GeometricBound
open scoped ENNReal
namespace Asakura

/-- The cancellation of the grid dimension in the Kolmogorov moment estimate. -/
theorem dyadic_dimension_cancellation (d m : ℕ) (p ε c : ℝ) (hp : 0 < p) :
    (((6 * (2:ℝ)^m)^d)^(1/p)) * (c * ((1/2:ℝ)^m)^(ε + d/p)) =
      c * (6:ℝ)^(d/p) * ((2:ℝ)^(-ε))^m := by
  have h2 : (0:ℝ) < 2^m := by positivity
  have h6 : (0:ℝ) < 6 * 2^m := by positivity
  have hcard : (((6 * (2:ℝ)^m)^d)^(1/p)) = (6:ℝ)^(d/p) * ((2:ℝ)^m)^(d/p) := by
    rw [← Real.rpow_natCast_mul h6.le]
    have he : (d:ℝ) * (1/p) = d/p := by ring
    rw [he, Real.mul_rpow (by norm_num) h2.le]
  have hmesh : ((1/2:ℝ)^m)^(ε + d/p) = ((2:ℝ)^m)^(-(ε + d/p)) := by
    rw [one_div_pow, one_div, Real.inv_rpow h2.le, ← Real.rpow_neg h2.le]
  have hcancel : ((2:ℝ)^m)^(d/p) * ((2:ℝ)^m)^(-(ε+d/p)) = ((2:ℝ)^m)^(-ε) := by
    rw [← Real.rpow_add h2]
    congr 1
    ring
  rw [hcard, hmesh]
  calc
    (6:ℝ)^(d/p) * (2^m)^(d/p) * (c * (2^m)^(-(ε+d/p))) =
        c * 6^(d/p) * ((2^m)^(d/p) * (2^m)^(-(ε+d/p))) := by ring
    _ = c * 6^(d/p) * (2^m)^(-ε) := by rw [hcancel]
    _ = c * 6^(d/p) * ((2:ℝ)^(-ε))^m := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
        mul_comm (m:ℝ) (-ε), Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
end Asakura
