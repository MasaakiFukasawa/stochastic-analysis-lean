import Chapter6DensityMartingale

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem conditional_density_trim {Ω:Type*} {G m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (hG:G≤m)
    (D:Ω → ℝ) (hi:Integrable D P) (hn:∀ᵐw∂P,0≤D w) :
    (P.withDensity (fun w => ENNReal.ofReal (D w))).trim hG=
      (P.withDensity (fun w => ENNReal.ofReal (P[D|G] w))).trim hG := by
  apply @Measure.ext Ω G
  intro A hA
  rw [trim_measurableSet_eq hG hA,trim_measurableSet_eq hG hA,
    withDensity_apply _ (hG A hA),withDensity_apply _ (hG A hA),
    ←ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_restrict_of_ae hn),
    ←ofReal_integral_eq_lintegral_ofReal integrable_condExp.integrableOn
      (ae_restrict_of_ae (condExp_nonneg hn)),setIntegral_condExp hG hi hA]

theorem conditional_density_integrable_iff {Ω:Type*} {G m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (hG:G≤m)
    (D:Ω → ℝ) (hi:Integrable D P) (hn:∀ᵐw∂P,0≤D w)
    (X:Ω → ℝ) (hX:StronglyMeasurable[G] X) :
    Integrable X (P.withDensity (fun w => ENNReal.ofReal (D w))) ↔
    Integrable X (P.withDensity (fun w => ENNReal.ofReal (P[D|G] w))) := by
  have he := conditional_density_trim P hG D hi hn
  constructor <;> intro hx
  · apply integrable_of_integrable_trim hG
    rw [←he]
    exact hx.trim hG hX
  · apply integrable_of_integrable_trim hG
    rw [he]
    exact hx.trim hG hX

theorem density_div_conditional_integrable {Ω:Type*} {G m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (hG:G≤m)
    (D:Ω → ℝ) (hi:Integrable D P) (hp:∀ᵐw∂P,0<D w)
    (Y:Ω → ℝ) (hY:StronglyMeasurable[G] Y) (hYi:Integrable Y P) :
    Integrable (fun w => Y w/P[D|G] w) (P.withDensity (fun w => ENNReal.ofReal (D w))) := by
  letI:MeasurableSpace Ω := m
  have hz := Asakura.FullAudit.exercise_ce_strictly_positive P hG hi hp
  have hm:Measurable (fun w => ENNReal.ofReal (P[D|G] w)) :=
    ENNReal.measurable_ofReal.comp (stronglyMeasurable_condExp.measurable.mono hG le_rfl)
  apply (conditional_density_integrable_iff P hG D hi (hp.mono (fun _ h => h.le)) _
    (hY.div stronglyMeasurable_condExp)).mpr
  apply (integrable_withDensity_iff_integrable_smul' hm (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply hYi.congr
  filter_upwards [hz] with w hw
  simp only [ENNReal.toReal_ofReal hw.le,smul_eq_mul]
  change Y w=P[D|G] w*(Y w/P[D|G] w)
  field_simp
end Asakura.Chapter13
#print axioms Asakura.Chapter13.density_div_conditional_integrable
