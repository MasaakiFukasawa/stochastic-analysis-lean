import Chapter12GaussianKernelMeasure

open Real
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem gaussian_fourier_normalization (d : ℕ) (b : ℝ) (hb : 0<b) :
    (π/b)^(d/2:ℝ)*(4*π*b)^(d/2:ℝ)=(2*π)^d := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have he : π/b*(4*π*b)=(2*π)^2 := by field_simp <;> ring
  rw [he,← Real.rpow_natCast ((2*π):ℝ) 2,← Real.rpow_mul (by positivity)]
  have hh : (2:ℝ)*(d/2)=d := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hh,Real.rpow_natCast]

theorem gaussian_scale_normalization (d : ℕ) (r : ℝ) (hr : 0<r) :
    (π/(1/(4*r^2)))^(d/2:ℝ)=r^d*(4*π)^(d/2:ℝ) := by
  have he : π/(1/(4*r^2))=r^2*(4*π) := by field_simp <;> ring
  rw [he,Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast r 2,← Real.rpow_mul hr.le]
  have hh : (2:ℝ)*(d/2)=d := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hh,Real.rpow_natCast]

end Asakura.Chapter12
