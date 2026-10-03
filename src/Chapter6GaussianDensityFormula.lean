import Chapter6PositiveDensityWritten
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open MeasureTheory ProbabilityTheory Matrix Finset
open scoped Topology BigOperators ENNReal NNReal Matrix
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

theorem gaussian_product_formula {d : ℕ} (t : ℝ≥0) (z : Fin d → ℝ) :
    (∏ i,gaussianPDFReal 0 t (z i))=
      (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹^d * Real.exp (-(∑ i,z i^2)/(2*(t:ℝ))) := by
  simp only [gaussianPDFReal_def,sub_zero,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
  rw [←Real.exp_sum]
  simp only [←sum_div,←sum_neg_distrib]

theorem covariance_matrix_quadratic {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) :
    (∑ i,(S⁻¹ *ᵥ z) i^2)=z ⬝ᵥ ((S*Sᵀ)⁻¹ *ᵥ z) := by
  rw [Matrix.mul_inv_rev,←Matrix.transpose_nonsing_inv,←Matrix.mulVec_mulVec,
    dotProduct_mulVec,←mulVec_transpose,Matrix.transpose_transpose]
  simp only [dotProduct,pow_two]

theorem covariance_matrix_sqrt_det {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Real.sqrt (Matrix.det (S*Sᵀ))=|S.det| := by
  rw [Matrix.det_mul,Matrix.det_transpose,←pow_two,Real.sqrt_sq_eq_abs]

theorem gaussian_sqrt_power (c : ℝ) (hc : 0≤c) (d : ℕ) :
    (Real.sqrt c)^d=c^((d:ℝ)/2) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hc]
  congr 1
  ring

end Asakura.Chapter6
