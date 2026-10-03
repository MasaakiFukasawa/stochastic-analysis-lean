import Chapter7CovarianceMatrixAlgebra
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators
namespace Asakura.Chapter7

/-- The deterministic Cauchy--Schwarz estimate for the drift remainder in
a single covariance entry. On a uniform grid n*h=T this is exactly the
bound by T times the modulus of continuity times the Brownian energy. -/
theorem drift_remainder_cauchy_schwarz {n : ℕ} (r y : Fin n → ℝ)
    (h ω : ℝ) (hh : 0 ≤ h) (hω : 0 ≤ ω) (hr : ∀ k,|r k| ≤ h*ω) :
    Real.sqrt n*|∑ k,r k*y k| ≤ (n:ℝ)*h*ω*Real.sqrt (∑ k,y k^2) := by
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hQ : 0 ≤ ∑ k,y k^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hsum : (∑ k,r k^2) ≤ (n:ℝ)*h^2*ω^2 := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      (sq_le_sq₀ (abs_nonneg (r k)) (mul_nonneg hh hω)).mpr (hr k))
    simp only [sq_abs,mul_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    convert hs using 1 <;> ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r y
  have hupper := hcs.trans (mul_le_mul_of_nonneg_right hsum hQ)
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg hn hh) hω) (Real.sqrt_nonneg _))).mp
  simp only [mul_pow,sq_abs,Real.sq_sqrt hn,Real.sq_sqrt hQ]
  have hs := mul_le_mul_of_nonneg_left hupper hn
  nlinarith only [hs]

end Asakura.Chapter7
