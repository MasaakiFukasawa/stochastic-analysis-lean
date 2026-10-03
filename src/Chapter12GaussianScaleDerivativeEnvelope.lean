import Chapter12GaussianScaleScoreBound

open Finset
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000

noncomputable def scaleEnvelopeConstant (d : ℕ) (C s : ℝ) (k : Fin d → ℝ) : ℝ :=
  |C| *(2/s)^d*Real.exp (s^2*(∑ i,(k i)^2)/2)

/-- A single integrable majorant can control the whole scale derivative. -/
theorem gaussian_scale_derivative_envelope {d : ℕ} (C s u : ℝ) (hs : 0<s)
    (hu : s/2≤u) (hu' : u≤2*s) (z k : Fin d → ℝ) :
    |scaleGaussianKernel C k z u*((∑ i,(z i)^2)/u^3-(d:ℝ)/u-u*(∑ i,(k i)^2)/4)|≤
      (scaleEnvelopeConstant d C s k*(8/s^3+2*(d:ℝ)/s+s*(∑ i,(k i)^2)/2))*
        ((1+∑ i,(z i)^2)*Real.exp (-(∑ i,(z i)^2)/(16*s^2))) := by
  have hk := scale_gaussian_kernel_envelope C s u hs hu hu' z k
  have hb := gaussian_scale_score_bound s u (∑ i,(z i)^2) (∑ i,(k i)^2) d hs hu hu'
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg _)
  rw [abs_mul]
  have hc : 0≤scaleEnvelopeConstant d C s k := by unfold scaleEnvelopeConstant; positivity
  have hh := mul_le_mul hk hb (abs_nonneg _) (mul_nonneg hc (Real.exp_nonneg _))
  dsimp [scaleEnvelopeConstant] at hh ⊢
  nlinarith [hh]

end Asakura.Chapter12
