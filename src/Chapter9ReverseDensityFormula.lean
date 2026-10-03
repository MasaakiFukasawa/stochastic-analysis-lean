import Chapter9BoundedPosterior
import Chapter9ContinuousDensityUniqueness
import Chapter9ActualForwardPDE

open MeasureTheory
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Identify the Bayes posterior with the manuscript's density ratio.
The denominator is identified pointwise from the actual marginal measures
and continuity, so no exceptional observation states remain. -/
theorem ou_posterior_density_formula {d : ℕ}
    (μ ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s t : ℝ) (hs : 0<s) (hst : s<t)
    (hν : ν=volume.withDensity (fun y => ENNReal.ofReal (∫ z,Real.exp (ouExponent z (s,y)) ∂μ)))
    (hmarg : volume.withDensity (fun y => ENNReal.ofReal (∫ z,Real.exp (ouExponent z (t,y)) ∂μ))=
      (volume : Measure (Fin d → ℝ)).withDensity (fun y => ENNReal.ofReal
        (∫ z,Real.exp (ouExponent z (t-s,y)) ∂ν)))
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    gaussianPosteriorTest ν (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) f x=
      (∫ y,f y*(∫ z,Real.exp (ouExponent z (s,y)) ∂μ)*
        gaussianKernel (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) y x)/
        (∫ z,Real.exp (ouExponent z (t,x)) ∂μ) := by
  have hp0 (r : ℝ) (y : Fin d → ℝ) : 0≤∫ z,Real.exp (ouExponent z (r,y)) ∂μ :=
    integral_nonneg (fun z => (Real.exp_pos _).le)
  have hq0 (y : Fin d → ℝ) : 0≤∫ z,Real.exp (ouExponent z (t-s,y)) ∂ν :=
    integral_nonneg (fun z => (Real.exp_pos _).le)
  have hden := continuous_density_unique _ _
    (ou_mixture_slice_smooth μ t (hs.trans hst)).continuous
    (ou_mixture_slice_smooth ν (t-s) (sub_pos.mpr hst)).continuous
    (hp0 t) hq0 hmarg
  unfold gaussianPosteriorTest
  have he : (∫ z,gaussianKernel (Real.exp (-(t-s))) (1-Real.exp (-2*(t-s))) z x ∂ν)=
      ∫ z,Real.exp (ouExponent z (t,x)) ∂μ := (congrFun hden x).symm
  rw [he,hν,integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro y
    simp only [ENNReal.toReal_ofReal (hp0 s y),smul_eq_mul]
    ring
  · exact (ou_mixture_slice_smooth μ s hs).continuous.measurable.ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
end Asakura.Chapter9
