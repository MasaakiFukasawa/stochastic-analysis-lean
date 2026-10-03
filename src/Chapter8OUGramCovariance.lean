import Chapter8VectorOUStationary
import Chapter4OUVariance

open Matrix MeasureTheory
open scoped BigOperators
namespace Asakura.Chapter8
open Asakura.Chapter4
set_option maxHeartbeats 1200000

/-- The possibly singular covariance is Sigma Sigma-transpose / 2. -/
theorem ou_gram_covariance {d n : ℕ} (σ : Matrix (Fin d) (Fin n) ℝ) :
    (((1/2:ℝ) • (σ*σᵀ)).PosSemidef) ∧
      ∀ v : Fin d → ℝ,v ⬝ᵥ (((1/2:ℝ) • (σ*σᵀ)) *ᵥ v)=
        (∑ j,(∑ i,v i*σ i j)^2)/2 := by
  constructor
  · have hh : (σ*σᵀ).PosSemidef := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose σ
    exact hh.smul (by norm_num : (0:ℝ)≤1/2)
  · intro v
    rw [smul_mulVec,dotProduct_smul,smul_eq_mul,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,
      Matrix.mulVec_transpose]
    simp only [dotProduct,vecMul,pow_two]
    ring

/-- The covariance of the scaled Ito convolution agrees with the OU
innovation covariance, for every projection. -/
theorem ou_projected_convolution_variance {d n : ℕ} (σ : Matrix (Fin d) (Fin n) ℝ)
    (v : Fin d → ℝ) (t : ℝ) :
    Real.exp (-t)^2*(∫ r in 0..t,∑ j,(∑ i,v i*(σ i j*Real.exp r))^2)=
      (1-Real.exp (-2*t))*(v ⬝ᵥ (((1/2:ℝ) • (σ*σᵀ)) *ᵥ v)) := by
  rw [(ou_gram_covariance σ).2]
  have he j r : (∑ i,v i*(σ i j*Real.exp r))=(∑ i,v i*σ i j)*Real.exp r := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (show Continuous (fun r : ℝ => ((∑ i,v i*σ i j)*Real.exp r)^2) by fun_prop).intervalIntegrable 0 t),Finset.mul_sum]
  have hvar j := ou_scaled_integral_variance 1 (∑ i,v i*σ i j) t (by norm_num)
  simp only [one_mul,neg_one_mul,mul_one] at hvar
  simp_rw [hvar]
  rw [←Finset.sum_div,←Finset.sum_mul]
  ring

end Asakura.Chapter8
