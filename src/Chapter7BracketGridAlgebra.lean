import Chapter7CovarianceMatrixAlgebra

namespace Asakura.Chapter7

/-- The incomplete last cell creates only an O(1/n) bias in the bracket.
This verifies the normalization and powers of T and n in the manuscript. -/
theorem bracket_grid_bias (n : ℕ) (hn : 0 < n) (T q r : ℝ)
    (hT : 0 < T) (hq : 0 ≤ q) (hr : 0 ≤ r) (hrh : r ≤ T/n) (k : ℕ) :
    |(2*(n:ℝ)*q/T^2)*((k:ℝ)*(T/n)^2+r^2)-
      (2*q/T)*((k:ℝ)*(T/n)+r)| ≤ 2*q/n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have he : (2*(n:ℝ)*q/T^2)*((k:ℝ)*(T/n)^2+r^2)-
      (2*q/T)*((k:ℝ)*(T/n)+r) = -(2*(n:ℝ)*q/T^2)*(r*(T/n-r)) := by
    field_simp
    <;> ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 2*(n:ℝ)*q/T^2),
    abs_of_nonneg (mul_nonneg hr (sub_nonneg.mpr hrh))]
  have hh : 0 ≤ T/(n:ℝ) := div_nonneg hT.le hnR.le
  have hb : r*(T/n-r) ≤ (T/n)^2 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrh)]
  calc
    _ ≤ (2*(n:ℝ)*q/T^2)*(T/n)^2 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp <;> ring

lemma bracket_grid_variance_scale (n : ℕ) (hn : 0 < n) (T K : ℝ) (hT : 0 < T) :
    (4*(n:ℝ)/T^2)^2*((n:ℝ)*K*(T/n)^4)=16*K/n := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

end Asakura.Chapter7
