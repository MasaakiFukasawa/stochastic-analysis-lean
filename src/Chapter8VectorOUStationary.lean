import Chapter8GaussianProjection
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000

/-- The Gaussian OU transition preserves its covariance even when that
covariance is singular. No density or inverse matrix is used. -/
theorem vector_ou_gaussian_invariant {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) (a : ℝ) (ha : a^2≤1) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).map (fun x => a • x)) ∗
      multivariateGaussian 0 ((1-a^2) • S)=multivariateGaussian 0 S := by
  have hR : ((1-a^2) • S).PosSemidef := hS.smul (sub_nonneg.mpr ha)
  apply Measure.ext_of_charFun
  funext v
  rw [charFun_conv,charFun_map_smul,charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hR,charFun_multivariateGaussian hS,←Complex.exp_add]
  congr 1
  simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub,
    WithLp.ofLp_smul,smul_mulVec,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  push_cast
  ring

/-- For the drift -x the innovation covariance is (1-exp(-2t)) times
the invariant covariance; the same formula covers zero noise. -/
theorem vector_ou_gaussian_invariant_time {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) (t : ℝ) (ht : 0≤t) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).map (fun x => Real.exp (-t) • x)) ∗
      multivariateGaussian 0 ((1-Real.exp (-2*t)) • S)=multivariateGaussian 0 S := by
  have he : Real.exp (-t)^2=Real.exp (-2*t) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hh := vector_ou_gaussian_invariant S hS (Real.exp (-t)) (by
    rw [he]
    exact Real.exp_le_one_iff.mpr (by linarith))
  simpa only [he] using hh

end Asakura.Chapter8
