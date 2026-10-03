import Chapter12ProductConditionalIntegral
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

/-- Integrating independent future variables constructs the conditional
expectation given the past, on the original probability space. -/
theorem independent_conditional_integral {Ω E G : Type*}
    [m : MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace G]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) (ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → E) (Y : Ω → G) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hind : IndepFun X Y P)
    (f : E × G → ℝ) (hfm : Measurable f) (hf : Integrable f (μ.prod ν)) :
    P[(fun w => f (X w,Y w))|MeasurableSpace.comap X inferInstance] =ᵐ[P]
      (fun w => ∫ y,f (X w,y) ∂ν) := by
  letI : MeasurableSpace Ω := m
  let F := MeasurableSpace.comap X inferInstance
  have hF : F≤m := hXm.comap_le
  have hXY := hind.hasLaw_prod hX hY
  let g := fun x => ∫ y,f (x,y) ∂ν
  have hgm : Measurable g := hfm.stronglyMeasurable.integral_prod_right'.measurable
  have hgi := hX.integrable_comp hf.integral_prod_left
  have hgp : Measurable[F] (fun w => g (X w)) := hgm.comp (comap_measurable X)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hF (hXY.integrable_comp hf)
    (fun s _ _ => hgi.integrableOn) ?_ hgp.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨a,ha,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hsX := setIntegral_map (μ := P) ha hgm.aestronglyMeasurable hXm.aemeasurable
  rw [hX.map_eq] at hsX
  have hsXY := setIntegral_map (μ := P) (ha.prod MeasurableSet.univ)
    hfm.aestronglyMeasurable (hXm.prodMk hYm).aemeasurable
  rw [hXY.map_eq] at hsXY
  change (∫ w in X ⁻¹' a,g (X w) ∂P)=(∫ w in X ⁻¹' a,f (X w,Y w) ∂P)
  rw [←hsX]
  rw [setIntegral_prod f hf.integrableOn] at hsXY
  simp only [Measure.restrict_univ] at hsXY
  have he : (fun w => (X w,Y w)) ⁻¹' (a ×ˢ univ)=X ⁻¹' a := by ext w; simp
  rw [he] at hsXY
  exact hsXY

end Asakura.Chapter12
