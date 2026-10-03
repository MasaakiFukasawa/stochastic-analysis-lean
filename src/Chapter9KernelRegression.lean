import Chapter9JointDensity

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Bayes formula for a normalized transition density relative to any
sigma-finite observation measure. A positive probability reference density
is introduced and then cancels, leaving exactly the manuscript's formula. -/
theorem kernel_regression {A B E : Type*}
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure A) (ν ρ : Measure B) [IsProbabilityMeasure μ] [SFinite ν]
    [IsProbabilityMeasure ρ]
    (φ : B → ℝ) (hφ : Measurable φ) (hφpos : ∀ y,0<φ y)
    (hρ : ρ=ν.withDensity (fun y => ENNReal.ofReal (φ y)))
    (k : A × B → ℝ) (hk : Measurable k) (hkpos : ∀ z,0<k z)
    (hki : ∀ x,Integrable (fun y => k (x,y)) ν)
    (hkone : ∀ x,(∫ y,k (x,y) ∂ν)=1)
    (f : A × B → E) (hmf : StronglyMeasurable f)
    (hf : Integrable f ((μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z)))) :
    let Q := (μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z))
    Q[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[Q]
      (fun z => (∫ x,k (x,z.2) ∂μ)⁻¹ • (∫ x,k (x,z.2) • f (x,z.2) ∂μ)) := by
  let Q := (μ.prod ν).withDensity (fun z => ENNReal.ofReal (k z))
  haveI : IsProbabilityMeasure Q := joint_density_probability μ ν k hk (fun z => (hkpos z).le) hki hkone
  let D := fun z => k z/φ z.2
  have hD : Measurable D := hk.div (hφ.comp measurable_snd)
  have hp z : 0<D z := div_pos (hkpos z) (hφpos z.2)
  have hQ : Q=(μ.prod ρ).withDensity (fun z => ENNReal.ofReal (D z)) := by
    rw [hρ]
    exact (joint_density_reference μ ν k hk (fun z => (hkpos z).le) φ hφ hφpos).symm
  have hiD : Integrable D (μ.prod ρ) := by
    have hi : Integrable (fun _ : A × B => (1 : ℝ)) Q := integrable_const _
    rw [hQ] at hi
    have hh := (integrable_withDensity_iff_integrable_smul'
      hD.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hi
    simpa only [ENNReal.toReal_ofReal (hp _).le,smul_eq_mul,mul_one] using hh
  have hb := vector_real_density_regression μ ρ Q D hD hiD hp hQ f hf hmf
  apply hb.trans
  apply ae_of_all
  intro z
  dsimp only [D]
  rw [integral_div]
  have hn : (∫ x,(k (x,z.2)/φ z.2) • f (x,z.2) ∂μ)=
      (φ z.2)⁻¹ • (∫ x,k (x,z.2) • f (x,z.2) ∂μ) := by
    simp_rw [div_eq_inv_mul,mul_smul]
    rw [integral_smul]
  rw [hn,smul_smul]
  congr 1
  rw [inv_div,div_eq_mul_inv]
  calc
    φ z.2*(∫ x,k (x,z.2) ∂μ)⁻¹*(φ z.2)⁻¹ =
      (φ z.2*(φ z.2)⁻¹)*(∫ x,k (x,z.2) ∂μ)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ (hφpos z.2).ne',one_mul]
end Asakura.Chapter9
