import Chapter9BoundedPosterior
import Chapter9ConditionalPullback

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Bayes regression for actual variables with the Gaussian transition
joint law. It is derived from the joint density and transported back to Ω. -/
theorem gaussian_transition_regression {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (U V : Ω → Fin d → ℝ) (hU : Measurable U) (hV : Measurable V)
    (a : ℝ) (v : ℝ≥0) (hv : v≠0)
    (hlaw : P.map (fun w => (U w,V w))=(μ.prod volume).withDensity
      (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2)))
    (f : (Fin d → ℝ) → ℝ) (hf : IsBoundedBorel f) :
    P[(fun w => f (U w))|MeasurableSpace.comap V inferInstance]=ᵐ[P]
      (fun w => gaussianPosteriorTest μ a v f (V w)) := by
  let Q := (μ.prod volume).withDensity (fun z => ENNReal.ofReal (gaussianKernel a v z.1 z.2))
  haveI : IsProbabilityMeasure Q := gaussian_joint_probability μ a v hv
  have hR := gaussian_posterior_bounded_borel μ a v hv f hf
  have hg : Measurable[MeasurableSpace.comap (Prod.snd : (Fin d → ℝ) × (Fin d → ℝ) → (Fin d → ℝ)) inferInstance]
      (fun z => gaussianPosteriorTest μ a v f z.2) := hR.1.comp (comap_measurable Prod.snd)
  have he := bounded_regression_pullback P Q (fun w => (U w,V w)) (hU.prodMk hV) hlaw
    (MeasurableSpace.comap Prod.snd inferInstance) measurable_snd.comap_le
    (fun z => f z.1) (fun z => gaussianPosteriorTest μ a v f z.2)
    (hf.comp Prod.fst measurable_fst) (hR.comp Prod.snd measurable_snd) hg
    (gaussian_joint_bounded_regression μ a v hv f hf)
  simpa only [MeasurableSpace.comap_comp,Function.comp_def] using he
end Asakura.Chapter9
