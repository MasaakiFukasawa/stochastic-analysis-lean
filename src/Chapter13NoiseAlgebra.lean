import Chapter13HJMAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped RealInnerProductSpace
namespace Asakura.Chapter13
set_option maxHeartbeats 1000000

theorem normalized_vector_norm {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x:E) (hx:x≠0) : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg x)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem normalized_vector_correlation {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y:E) : inner ℝ ((‖x‖⁻¹:ℝ) • x) ((‖y‖⁻¹:ℝ) • y)=inner ℝ x y/(‖x‖*‖y‖) := by
  simp only [inner_smul_left,inner_smul_right,conj_trivial]
  ring

theorem normalization_recovers_vector {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x:E) (hx:x≠0) (γ:ℝ) : (γ*‖x‖) • ((‖x‖⁻¹:ℝ) • x)=γ • x := by
  rw [smul_smul]
  congr 1
  field_simp

theorem covariance_diagonal_sqrt (γ s:ℝ) (hs:0≤s) : Real.sqrt (γ*γ*s*s)=|γ| * s := by
  rw [show γ*γ*s*s=(γ*s)^2 by ring,Real.sqrt_sq_eq_abs,abs_mul,abs_of_nonneg hs]

theorem covariance_correlation_identification (a b s t ρ:ℝ)
    (ha:a≠0) (hb:b≠0) (hs:0<s) (ht:0<t) :
    ρ=SignType.sign (a*b) * ((a*b*s*t*ρ)/Real.sqrt ((a*a*s*s)*(b*b*t*t))) := by
  rw [show (a*a*s*s)*(b*b*t*t)=(a*b*s*t)^2 by ring,Real.sqrt_sq_eq_abs]
  rw [abs_mul,abs_mul,abs_of_pos hs,abs_of_pos ht]
  have hab:a*b≠0 := mul_ne_zero ha hb
  have hsign: (SignType.sign (a*b):ℝ)*|a*b|=a*b := sign_mul_abs _
  have habs: |a*b|≠0 := abs_ne_zero.mpr hab
  field_simp
  have hh : (a*b)*(SignType.sign (a*b):ℝ)=|a*b| := by simpa [mul_comm] using (sign_mul_self (a*b))
  rw [← hh]
  ring

end Asakura.Chapter13
#print axioms Asakura.Chapter13.normalized_vector_norm
#print axioms Asakura.Chapter13.normalized_vector_correlation
#print axioms Asakura.Chapter13.normalization_recovers_vector
#print axioms Asakura.Chapter13.covariance_diagonal_sqrt
#print axioms Asakura.Chapter13.covariance_correlation_identification
