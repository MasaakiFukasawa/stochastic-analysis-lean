import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Conditional expectation on the past coordinate is obtained by integrating
the independent future coordinate. In the cylindrical application the second
measure is the finite-dimensional Gaussian law. -/
theorem product_conditional_integral {E G : Type*}
    [mE : MeasurableSpace E] [mG : MeasurableSpace G]
    (μ : Measure E) (ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E × G → ℝ) (hfm : Measurable f) (hf : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f|MeasurableSpace.comap (Prod.fst : E × G → E) inferInstance] =ᵐ[μ.prod ν]
      (fun z => ∫ y,f (z.1,y) ∂ν) := by
  let F := MeasurableSpace.comap (Prod.fst : E × G → E) inferInstance
  letI : MeasurableSpace (E × G) := mE.prod mG
  have hF : F ≤ mE.prod mG := measurable_fst.comap_le
  let g := fun x => ∫ y,f (x,y) ∂ν
  have hgm : Measurable g := hfm.stronglyMeasurable.integral_prod_right'.measurable
  have hgi : Integrable (fun z : E × G => g z.1) (μ.prod ν) := hf.integral_prod_left.comp_fst ν
  have hgp : Measurable[F] (fun z : E × G => g z.1) := hgm.comp (comap_measurable Prod.fst)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hF hf
    (fun s _ _ => hgi.integrableOn) ?_ hgp.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨a,ha,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have he : (Prod.fst : E × G → E) ⁻¹' a=a ×ˢ univ := by ext z; simp
  rw [he,setIntegral_prod _ hgi.integrableOn,setIntegral_prod _ hf.integrableOn]
  simp only [setIntegral_univ,integral_const,Measure.restrict_univ,probReal_univ,one_smul,g]

end Asakura.Chapter12
