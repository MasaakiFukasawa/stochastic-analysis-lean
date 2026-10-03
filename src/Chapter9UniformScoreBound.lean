import Chapter9ScoreLipschitz
import Chapter9GaussianKernel

open MeasureTheory
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 500000

/-- Uniform-in-time estimate: only a lower variance bound and an upper
bound one on the squared attenuation are needed. -/
theorem radial_velocity_uniform_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure E) [IsProbabilityMeasure μ]
    (c a v w R : ℝ) (hc : 0<c) (hw : 0<w) (hwv : w≤v) (ha : a^2≤1)
    (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R) :
    LipschitzWith ⟨1+1/w+R^2/w^2,by positivity⟩
      (fun y => -y-(∫ x,radialKernel c a v x y ∂μ)⁻¹ •
        (∫ x,(-radialKernel c a v x y/v) • (y-a • x) ∂μ)) := by
  have hv := hw.trans_le hwv
  apply (radial_probability_velocity_lipschitz μ c a v hc hv R hR hb).weaken
  change 1+(1/v+a^2/v^2*R^2) ≤ 1+1/w+R^2/w^2
  have h1 : 1/v≤1/w := one_div_le_one_div_of_le hw hwv
  have h2 : a^2/v^2≤1/w^2 :=
    (div_le_div_of_nonneg_right ha (sq_nonneg v)).trans
      (one_div_le_one_div_of_le (sq_pos_of_pos hw) (sq_le_sq₀ hw.le hv.le |>.mpr hwv))
  have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg R)
  nlinarith [show 1/w^2*R^2=R^2/w^2 by ring]

/-- OU coefficients on every strip t≥epsilon obey the bounds used above. -/
theorem ou_strip_parameters (ε t : ℝ) (hε : 0<ε) (ht : ε≤t) :
    0<1-Real.exp (-2*ε) ∧ 1-Real.exp (-2*ε)≤1-Real.exp (-2*t) ∧
      (Real.exp (-t))^2≤1 := by
  refine ⟨ou_variance_positive ε hε,?_,?_⟩
  · have h := Real.exp_le_exp.mpr (show -2*t≤-2*ε by linarith)
    linarith
  · have he : Real.exp (-t)≤1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-t)]
end Asakura.Chapter9
