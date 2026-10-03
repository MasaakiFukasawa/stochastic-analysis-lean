import FullAuditBayes
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Conditioning a jointly integrable function on the second coordinate
of a product probability space integrates out the first coordinate. -/
theorem product_conditional_integral {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (hm : StronglyMeasurable f) (hi : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[μ.prod ν]
      (fun z => ∫ x,f (x,z.2) ∂μ) := by
  let G := MeasurableSpace.comap (Prod.snd : A × B → B) inferInstance
  have hle : G ≤ @Prod.instMeasurableSpace A B mA mB := (@measurable_snd A B mA mB).comap_le
  letI : MeasurableSpace (A × B) := @Prod.instMeasurableSpace A B mA mB
  have hib : Integrable (fun z : A × B => ∫ x,f (x,z.2) ∂μ) (μ.prod ν) :=
    hi.integral_prod_right.comp_snd μ
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hi
    (fun _ _ _ => hib.integrableOn) _
    (hm.integral_prod_left'.comp_measurable (show Measurable[G] (Prod.snd : A × B → B) from (fun S hS => ⟨S,hS,rfl⟩))).aestronglyMeasurable
  intro E hE _
  rcases hE with ⟨S,hS,rfl⟩
  have hpre : MeasurableSet ((Prod.snd : A × B → B) ⁻¹' S) := measurable_snd hS
  rw [←integral_indicator hpre,←integral_indicator hpre,
    integral_prod_symm _ (hib.indicator hpre),integral_prod_symm _ (hi.indicator hpre)]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  by_cases hy : y∈S <;> simp [Set.indicator,hy]


/-- Bayes regression from an actual positive joint density, with a
probability reference measure in each coordinate. The kernel used by the
manuscript is obtained by dividing its Lebesgue density by a positive
Gaussian reference density; that factor cancels in this ratio. -/
theorem density_regression_ratio {A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (A × B)) [IsProbabilityMeasure Q]
    (D f : A × B → ℝ) (hD : Measurable D) (hiD : Integrable D (μ.prod ν))
    (hpos : ∀ᵐ z ∂μ.prod ν,0<D z)
    (hQ : Q=(μ.prod ν).withDensity (fun z => ENNReal.ofReal (D z)))
    (hf : Integrable f Q) (hDf : StronglyMeasurable (fun z => D z*f z)) :
    Q[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[μ.prod ν]
      (fun z => (∫ x,D (x,z.2)*f (x,z.2) ∂μ)/(∫ x,D (x,z.2) ∂μ)) := by
  have hDi : Integrable (fun z => D z*f z) (μ.prod ν) := by
    have hh := hf
    rw [hQ] at hh
    have hnon : ∀ᵐ z ∂μ.prod ν,0≤D z := hpos.mono (fun _ h => h.le)
    have hh' := (integrable_withDensity_iff_integrable_smul'
      (μ := μ.prod ν) hD.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hh
    apply hh'.congr
    filter_upwards [hnon] with z hz
    simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]
  have hb := Asakura.FullAudit.bayes_real_density (μ.prod ν) Q measurable_snd.comap_le D hD hiD hpos hQ f hf
  have h0 := product_conditional_integral μ ν D hD.stronglyMeasurable hiD
  have h1 := product_conditional_integral μ ν (fun z => D z*f z) hDf hDi
  filter_upwards [hb,h0,h1] with z hb h0 h1
  rw [hb,h0,h1]
end Asakura.Chapter9
