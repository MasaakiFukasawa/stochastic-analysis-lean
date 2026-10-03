import EndToEndGaussianSmoothing

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

lemma density_integral_one {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (p : E → ℝ) (hp : Measurable p) (hpos : ∀ x,0 ≤ p x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x)))] :
    Integrable p μ ∧ (∫ x,p x ∂μ)=1 := by
  have hi : (∫⁻ x,ENNReal.ofReal (p x) ∂μ)=1 := by
    simpa only [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      using (measure_univ : μ.withDensity (fun x => ENNReal.ofReal (p x)) univ=1)
  have hf := integrable_toReal_of_lintegral_ne_top hp.ennreal_ofReal.aemeasurable (by rw [hi]; simp)
  simp only [ENNReal.toReal_ofReal (hpos _)] at hf
  refine ⟨hf,?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hf (.of_forall hpos)
  rw [hi] at he
  exact ENNReal.ofReal_eq_one.mp he

lemma gaussian_mixture_probability_density {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (b : ℝ) (hb : 0 < b) :
    let p := fun x => ∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂μ
    Continuous p ∧ (∀ x,0 ≤ p x) ∧ Integrable p volume ∧ (∫ x,p x)=1 := by
  have hg := normalized_gaussian_kernel_properties (E:=E) (1/(4*b)) (by positivity)
  let γ := volume.withDensity (fun x : E => ENNReal.ofReal (normalizedGaussianKernel (1/(4*b)) x))
  letI : IsProbabilityMeasure γ := hg.2.2.2.2.2
  obtain ⟨he,hc,hp,hbnd⟩ := real_mixture_density μ volume _ hg.1 (fun x => (hg.2.1 x).le) _ hg.2.2.1
  have hmap : IsProbabilityMeasure ((μ.prod γ).map (fun z : E × E => z.1+z.2)) :=
    (Measure.isProbabilityMeasure_map_iff (show AEMeasurable (fun z : E × E => z.1+z.2) (μ.prod γ) by fun_prop)).mpr inferInstance
  rw [show (μ.prod γ).map (fun z : E × E => z.1+z.2)=_ from he] at hmap
  letI := hmap
  exact ⟨hc,hp,density_integral_one volume _ hc.measurable hp⟩

/-- Fixed-variance Gaussian smoothing converges in L1, without tightness or
 Levy's continuity theorem as an input. -/
theorem gaussian_smoothing_L1 {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hlim : ∀ ξ,Tendsto (fun n => charFun (μ n) ξ) atTop (𝓝 (charFun ν ξ)))
    (b : ℝ) (hb : 0 < b) :
    Tendsto (fun n => ∫ x,|(∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂μ n)-
      (∫ y,normalizedGaussianKernel (1/(4*b)) (x-y) ∂ν)|) atTop (𝓝 0) := by
  have hp n := gaussian_mixture_probability_density (μ n) b hb
  have hq := gaussian_mixture_probability_density ν b hb
  exact probability_density_L1 volume _ _ (fun n => (hp n).2.2.1) hq.2.2.1
    (fun n => .of_forall (hp n).2.1) (.of_forall hq.2.1)
    (fun n => (hp n).2.2.2) hq.2.2.2 (.of_forall (gaussian_smoothing_pointwise μ ν hlim b hb))

#print axioms density_integral_one
#print axioms gaussian_mixture_probability_density
#print axioms gaussian_smoothing_L1
end Asakura.EndToEnd
