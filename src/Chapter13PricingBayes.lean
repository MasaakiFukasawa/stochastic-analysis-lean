import Chapter13NormalizedDensity

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem numeraire_payoff_pricing {Ω:Type*} {G m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] (hG:G≤m)
    (Z:Ω → ℝ) (hZm:Measurable Z) (hZi:Integrable Z P) (hZp:∀ᵐw∂P,0<Z w)
    (F:Ω → ℝ) (hZF:Integrable (fun w => Z w*F w) P) :
    let c:=∫w,Z w∂P
    let Q:=P.withDensity (fun w => ENNReal.ofReal (Z w/c))
    IsProbabilityMeasure Q ∧ Integrable F Q ∧
      P[(fun w => Z w*F w)|G]=ᵐ[P] (fun w => P[Z|G] w*Q[F|G] w) := by
  letI:MeasurableSpace Ω := m
  intro c Q
  obtain ⟨hc,hDm,hDi,hDp,hDone,hQ⟩ := normalized_density_probability P Z hZm hZi hZp
  letI := hQ
  let D:=fun w => Z w/c
  have hDF:Integrable (fun w => D w*F w) P := by
    convert hZF.div_const c using 1
    funext w
    dsimp [D]
    ring
  have hFi:Integrable F Q := by
    apply (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp hDm)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
    apply hDF.congr
    filter_upwards [hDp] with w hw
    simp only [Function.comp_def,ENNReal.toReal_ofReal hw.le,smul_eq_mul]
    rfl
  have hb:=Asakura.FullAudit.bayes_real_density P Q hG D hDm hDi hDp rfl F hFi
  have hDce:=condExp_smul (μ:=P) c⁻¹ Z G
  have hDFce:=condExp_smul (μ:=P) c⁻¹ (fun w => Z w*F w) G
  have hDe:D=fun w => c⁻¹*Z w := by funext w;dsimp [D];ring
  have hDFe:(fun w => D w*F w)=(fun w => c⁻¹*(Z w*F w)) := by funext w;dsimp [D];ring
  have hz:=Asakura.FullAudit.exercise_ce_strictly_positive P hG hZi hZp
  refine ⟨hQ,hFi,?_⟩
  filter_upwards [hb,hDce,hDFce,hz] with w hb hd hdf hz
  change P[(fun w => c⁻¹*Z w)|G] w=c⁻¹*P[Z|G] w at hd
  change P[(fun w => c⁻¹*(Z w*F w))|G] w=c⁻¹*P[(fun w => Z w*F w)|G] w at hdf
  rw [hDFe,hDe,hd,hdf] at hb
  rw [hb]
  have hc0:c≠0 := ne_of_gt hc
  field_simp
end Asakura.Chapter13
#print axioms Asakura.Chapter13.numeraire_payoff_pricing
