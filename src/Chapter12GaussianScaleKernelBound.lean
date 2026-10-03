import Chapter12GaussianScaleEnvelope
import Chapter12GaussianScaleKernelDerivative

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem gaussian_scale_prefactor_bound (d : ℕ) (s u : ℝ) (hs : 0<s) (hu : s/2≤u) :
    Real.exp (-(d:ℝ)*Real.log u)≤(2/s)^d := by
  have hup : 0<u := by linarith
  have he : Real.exp (-(d:ℝ)*Real.log u)=(1/u)^d := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hup,one_div,inv_pow]
  rw [he]
  apply pow_le_pow_left₀ (by positivity)
  have hh := one_div_le_one_div_of_le (by linarith : 0<s/2) hu
  convert hh using 1 <;> field_simp <;> ring

theorem scale_gaussian_kernel_envelope {d : ℕ} (C s u : ℝ) (hs : 0<s)
    (hu : s/2≤u) (hu' : u≤2*s) (z k : Fin d → ℝ) :
    |scaleGaussianKernel C k z u|≤
      (|C| *(2/s)^d*Real.exp (s^2*(∑ i,(k i)^2)/2))*
        Real.exp (-(∑ i,(z i)^2)/(16*s^2)) := by
  have hpre := gaussian_scale_prefactor_bound d s u hs hu
  have hexp := gaussian_scale_exponential_envelope s u hs hu hu' z k
  unfold scaleGaussianKernel
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-(d:ℝ)*Real.log u-(∑ i,(z i/u+u*k i/2)^2)/2)=
      Real.exp (-(d:ℝ)*Real.log u)*Real.exp (-(∑ i,(z i/u+u*k i/2)^2)/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc
    _≤|C| *((2/s)^d*(Real.exp (s^2*(∑ i,(k i)^2)/2)*Real.exp (-(∑ i,(z i)^2)/(16*s^2)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hpre hexp (Real.exp_nonneg _) (by positivity)) (abs_nonneg C)
    _=_ := by ring

end Asakura.Chapter12
