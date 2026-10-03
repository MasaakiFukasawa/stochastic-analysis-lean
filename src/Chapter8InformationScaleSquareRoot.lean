import Chapter8InformationSquareRoot

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000

/-- The observable normalisation in the manuscript is exactly the
normalised-information square root times the scaled estimation error. -/
theorem information_scaled_square_root {p : ℕ} (I : Matrix (Fin p) (Fin p) ℝ)
    (hI : I.PosSemidef) (T : ℝ) (hT : 0<T) (v : EuclideanSpace ℝ (Fin p)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (T⁻¹ • I)) (Real.sqrt T • v)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt I) v := by
  have hs : CFC.sqrt (T⁻¹ • I)=Real.sqrt (T⁻¹) • CFC.sqrt I := by
    apply (CFC.sqrt_eq_iff _ _ (smul_nonneg (inv_nonneg.mpr hT.le) hI.nonneg)
      (smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg I))).mpr
    rw [smul_mul_smul,CFC.sqrt_mul_sqrt_self I hI.nonneg,←pow_two,Real.sq_sqrt (inv_nonneg.mpr hT.le)]
  rw [hs,map_smul,map_smul,ContinuousLinearMap.smul_apply,smul_smul,Real.sqrt_inv,mul_inv_cancel₀ (Real.sqrt_pos.mpr hT).ne',one_smul]
end Asakura.Chapter8
