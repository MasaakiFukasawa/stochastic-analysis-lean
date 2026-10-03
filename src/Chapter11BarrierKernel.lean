import Chapter4GaussianPayoff

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 1500000

/-- The image term divided by the original Gaussian kernel, with the actual
normal density (including its normalization). -/
theorem barrier_gaussian_image_identity (a θ ν y z : ℝ) (v : ℝ≥0) (hv : v≠0)
    (hν : ν*(v:ℝ)=2*a*θ) :
    Real.exp (-ν*y)*gaussianPDFReal (-y+a*θ) v z=
      Real.exp (-2*y*z/(v:ℝ))*gaussianPDFReal (y+a*θ) v z := by
  have hv0 : (v:ℝ)≠0 := by exact_mod_cast hv
  have he : -ν*y+(-(z-(-y+a*θ))^2/(2*(v:ℝ)))=
      -2*y*z/(v:ℝ)+(-(z-(y+a*θ))^2/(2*(v:ℝ))) := by
    rw [(eq_div_iff hv0).mpr hν]
    field_simp
    ring
  simp only [gaussianPDFReal]
  calc
    _ = (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹*
        Real.exp (-ν*y+(-(z-(-y+a*θ))^2/(2*(v:ℝ)))) := by rw [Real.exp_add];ring
    _ = (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹*
        Real.exp (-2*y*z/(v:ℝ)+(-(z-(y+a*θ))^2/(2*(v:ℝ)))) := by rw [he]
    _ = _ := by rw [Real.exp_add];ring

/-- Both arguments below the barrier give a nonnegative killed density,
bounded above by the original transition density. -/
theorem barrier_gaussian_kernel_bounds (a θ ν y z : ℝ) (v : ℝ≥0) (hv : v≠0)
    (hν : ν*(v:ℝ)=2*a*θ) (hy : y≤0) (hz : z≤0) :
    0≤gaussianPDFReal (y+a*θ) v z-Real.exp (-ν*y)*gaussianPDFReal (-y+a*θ) v z ∧
      gaussianPDFReal (y+a*θ) v z-Real.exp (-ν*y)*gaussianPDFReal (-y+a*θ) v z≤
        gaussianPDFReal (y+a*θ) v z := by
  rw [barrier_gaussian_image_identity a θ ν y z v hv hν]
  have hnon : 0≤gaussianPDFReal (y+a*θ) v z := gaussianPDFReal_nonneg _ _ _
  have hp : 0≤y*z := mul_nonneg_of_nonpos_of_nonpos hy hz
  have he : Real.exp (-2*y*z/(v:ℝ))≤1 := Real.exp_le_one_iff.mpr (by
    apply div_nonpos_of_nonpos_of_nonneg _ v.property
    nlinarith)
  have hle := mul_le_mul_of_nonneg_right he hnon
  have hlo := mul_nonneg (Real.exp_pos (-2*y*z/(v:ℝ))).le hnon
  constructor <;> nlinarith

end Asakura.Chapter11
