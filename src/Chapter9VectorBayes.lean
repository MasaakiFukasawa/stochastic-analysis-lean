import Chapter9ProductConditional

open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Bochner-valued Bayes formula, with integrability under the changed
probability measure only. The numerator is proved integrable from the density. -/
theorem vector_bayes {Ω E : Type*} {G m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hG : G ≤ m) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun w => (d w : ℝ)) P)
    (hdpos : ∀ᵐ w ∂P,0<(d w : ℝ))
    (hQ : Q=P.withDensity (fun w => (d w : ℝ≥0∞)))
    (X : Ω → E) (hX : Integrable X Q) :
    Q[X|G] =ᵐ[P] fun w => (P[(fun w => (d w : ℝ))|G] w)⁻¹ •
      P[(fun w => (d w : ℝ) • X w)|G] w := by
  letI : MeasurableSpace Ω := m
  let D := fun w => (d w : ℝ)
  let Y := Q[X|G]
  have hYi : Integrable Y Q := integrable_condExp
  have hDX : Integrable (fun w => D w • X w) P := by
    rw [hQ] at hX
    exact (integrable_withDensity_iff_integrable_coe_smul hd).mp hX
  have hDY : Integrable (fun w => D w • Y w) P := by
    rw [hQ] at hYi
    exact (integrable_withDensity_iff_integrable_coe_smul hd).mp hYi
  have hchange (f : Ω → E) (A : Set Ω) (hA : MeasurableSet A) :
      (∫ w in A,f w ∂Q)=∫ w in A,D w • f w ∂P := by
    rw [hQ]
    exact setIntegral_withDensity_eq_setIntegral_smul hd f hA
  have heq : P[(fun w => D w • Y w)|G] =ᵐ[P] P[(fun w => D w • X w)|G] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hG hDX
      (fun A _ _ => integrable_condExp.integrableOn) _ stronglyMeasurable_condExp.aestronglyMeasurable
    intro A hA _
    rw [setIntegral_condExp hG hDY hA,←hchange Y A (hG A hA),←hchange X A (hG A hA)]
    exact setIntegral_condExp hG hX hA
  have hpull := condExp_smul_of_aestronglyMeasurable_right (m := G)
    hdi hDY (stronglyMeasurable_condExp (μ := Q) (m := G) (f := X)).aestronglyMeasurable
  have hpos := Asakura.FullAudit.exercise_ce_strictly_positive P hG hdi hdpos
  filter_upwards [heq,hpull,hpos] with w hEq hPull hPos
  change Y w=_
  change P[(fun w => D w • Y w)|G] w=P[D|G] w • Y w at hPull
  rw [←hEq,hPull,smul_smul,inv_mul_cancel₀ hPos.ne',one_smul]

theorem vector_product_conditional {A B E : Type*}
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → E) (hm : StronglyMeasurable f) (hi : Integrable f (μ.prod ν)) :
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
    (hm.integral_prod_left'.comp_measurable (show Measurable[G] (Prod.snd : A × B → B)
      from (fun S hS => ⟨S,hS,rfl⟩))).aestronglyMeasurable
  intro S hS _
  rcases hS with ⟨C,hC,rfl⟩
  have hpre : MeasurableSet ((Prod.snd : A × B → B) ⁻¹' C) := measurable_snd hC
  rw [←integral_indicator hpre,←integral_indicator hpre,
    integral_prod_symm _ (hib.indicator hpre),integral_prod_symm _ (hi.indicator hpre)]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  by_cases hy : y∈C <;> simp [Set.indicator,hy]

/-- Condition the actual joint density on its observation coordinate.
The conclusion holds under the joint law Q, as needed for the loss identity. -/
theorem vector_density_regression {A B E : Type*}
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (A × B)) [IsProbabilityMeasure Q]
    (d : A × B → ℝ≥0) (hd : Measurable d)
    (hdi : Integrable (fun z => (d z : ℝ)) (μ.prod ν))
    (hpos : ∀ᵐ z ∂μ.prod ν,0<(d z : ℝ))
    (hQ : Q=(μ.prod ν).withDensity (fun z => (d z : ℝ≥0∞)))
    (f : A × B → E) (hf : Integrable f Q)
    (hDf : StronglyMeasurable (fun z => (d z : ℝ) • f z)) :
    Q[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[Q]
      (fun z => (∫ x,(d (x,z.2) : ℝ) ∂μ)⁻¹ •
        (∫ x,(d (x,z.2) : ℝ) • f (x,z.2) ∂μ)) := by
  have hi : Integrable (fun z => (d z : ℝ) • f z) (μ.prod ν) := by
    have hh := hf
    rw [hQ] at hh
    exact (integrable_withDensity_iff_integrable_coe_smul hd).mp hh
  have hb := vector_bayes (μ.prod ν) Q measurable_snd.comap_le d hd hdi hpos hQ f hf
  have h0 := product_conditional_integral μ ν (fun z => (d z : ℝ))
    hd.coe_nnreal_real.stronglyMeasurable hdi
  have h1 := vector_product_conditional μ ν (fun z => (d z : ℝ) • f z) hDf hi
  have hbase : Q[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[μ.prod ν]
      (fun z => (∫ x,(d (x,z.2) : ℝ) ∂μ)⁻¹ •
        (∫ x,(d (x,z.2) : ℝ) • f (x,z.2) ∂μ)) := by
    filter_upwards [hb,h0,h1] with z hb h0 h1
    rw [hb,h0,h1]
  have hac : Q ≪ μ.prod ν := by
    rw [hQ]
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le hbase

theorem vector_real_density_regression {A B E : Type*}
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (A × B)) [IsProbabilityMeasure Q]
    (D : A × B → ℝ) (hD : Measurable D)
    (hdi : Integrable D (μ.prod ν)) (hpos : ∀ z,0<D z)
    (hQ : Q=(μ.prod ν).withDensity (fun z => ENNReal.ofReal (D z)))
    (f : A × B → E) (hf : Integrable f Q) (hmf : StronglyMeasurable f) :
    Q[f|MeasurableSpace.comap Prod.snd inferInstance] =ᵐ[Q]
      (fun z => (∫ x,D (x,z.2) ∂μ)⁻¹ • (∫ x,D (x,z.2) • f (x,z.2) ∂μ)) := by
  let d := fun z => (D z).toNNReal
  have he z : (d z : ℝ)=D z := Real.coe_toNNReal _ (hpos z).le
  have hd : Measurable d := hD.real_toNNReal
  have hi : Integrable (fun z => (d z : ℝ)) (μ.prod ν) := by simpa only [he] using hdi
  have hp : ∀ᵐ z ∂μ.prod ν,0<(d z : ℝ) := ae_of_all _ (fun z => by rw [he]; exact hpos z)
  have hdf : StronglyMeasurable (fun z => (d z : ℝ) • f z) :=
    hd.coe_nnreal_real.stronglyMeasurable.smul hmf
  have hh := vector_density_regression μ ν Q d hd hi hp hQ f hf hdf
  simpa only [he] using hh
end Asakura.Chapter9
