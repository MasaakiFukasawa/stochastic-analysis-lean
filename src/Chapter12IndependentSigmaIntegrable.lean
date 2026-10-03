import Chapter12IndependentSigmaIntegral

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Only integrability of the original random variable is required;
independence supplies the product-space integrability. -/
theorem independent_sigma_integral_of_integrable {Ω E : Type*}
    [m : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hle : F≤m)
    (Y : Ω → E) (hY : Measurable[m] Y) (ν : Measure E) [IsProbabilityMeasure ν]
    (hlaw : @HasLaw Ω E m mE Y ν P) (hind : Indep (MeasurableSpace.comap Y mE) F P)
    (f : Ω × E → ℝ) (hf : @Measurable _ _ (F.prod mE) inferInstance f)
    (hi : Integrable (fun w => f (w,Y w)) P) :
    P[(fun w => f (w,Y w))|F]=ᵐ[P] (fun w => ∫ y,f (w,y) ∂ν) := by
  letI := @probability_trim Ω m P _ F hle
  have hid := @trim_identity_preserving Ω m P F hle
  have hInd : @IndepFun Ω Ω E m F mE id Y P := by
    change Indep (MeasurableSpace.comap id F) (MeasurableSpace.comap Y mE) P
    simpa only [MeasurableSpace.comap_id] using hind.symm
  have hXY := hInd.hasLaw_prod hid.hasLaw hlaw
  have hip : Integrable[F.prod mE] f
      (@Measure.prod Ω E F mE (P.trim hle) ν) := by
    rw [← hXY.map_eq]
    exact (integrable_map_measure hf.aestronglyMeasurable hXY.aemeasurable).mpr hi
  exact @independent_sigma_integral Ω E m mE P _ F hle Y hY ν _ hlaw hind f hf hip

end Asakura.Chapter12
#print axioms Asakura.Chapter12.independent_sigma_integral_of_integrable
