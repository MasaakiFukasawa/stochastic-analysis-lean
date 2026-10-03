import Chapter2L2BochnerPointwise

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter13
open Asakura.Chapter2Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- An a.e. parameter identification suffices for the pointwise form of
an L2-valued Bochner integral. No choices on exceptional parameters are needed. -/
theorem l2_bochner_pointwise_ae {E S:Type*} [MeasurableSpace E] [MeasurableSpace S]
    (μ:Measure E) [SigmaFinite μ] (ν:Measure S) [SigmaFinite ν]
    (H:E × S → ℝ) (hm:Measurable H) (Z:E → Lp ℝ 2 ν) (hi:Integrable Z μ)
    (he:∀ᵐx∂μ,(Z x:S → ℝ)=ᵐ[ν] (fun s => H (x,s))) :
    ((∫x,Z x∂μ:Lp ℝ 2 ν):S → ℝ)=ᵐ[ν] (fun s => ∫x,H (x,s)∂μ) := by
  have hp (B:Set S) (hB:MeasurableSet B) (hf:ν B<∞):Integrable H (μ.prod (ν.restrict B)) := by
    letI:IsFiniteMeasure (ν.restrict B):=⟨by simpa using hf⟩
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [he] with x hx
      exact (((MeasureTheory.Lp.memLp (Z x)).ae_eq hx).restrict B).integrable (by norm_num)
    · apply (hi.norm.const_mul ‖indicatorConstLp 2 hB hf.ne (1:ℝ)‖).mono'
        (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      filter_upwards [he] with x hx
      have hl:MemLp (fun s => H (x,s)) 2 ν := (MeasureTheory.Lp.memLp (Z x)).ae_eq hx
      have hz:hl.toLp (fun s => H (x,s))=Z x := by
        apply Lp.ext
        exact hl.coeFn_toLp.trans hx.symm
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      simpa only [hz] using l2_set_integral_norm_bound ν B hB hf.ne _ hl
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro B hB hf
    exact integrableOn_Lp_of_measure_ne_top (∫x,Z x∂μ) (by norm_num) hf.ne
  · intro B hB hf
    exact (hp B hB hf).integral_prod_right
  · intro B hB hf
    rw [l2_set_integral_eq_inner ν B hB hf.ne]
    have hc := (innerSL ℝ (indicatorConstLp 2 hB hf.ne (1:ℝ))).integral_comp_comm hi
    change (∫x,inner ℝ (indicatorConstLp 2 hB hf.ne (1:ℝ)) (Z x)∂μ)=inner ℝ (indicatorConstLp 2 hB hf.ne (1:ℝ)) (∫x,Z x∂μ) at hc
    rw [←hc]
    calc
      (∫x,inner ℝ (indicatorConstLp 2 hB hf.ne (1:ℝ)) (Z x)∂μ) = ∫x,∫s in B,H (x,s)∂ν∂μ := by
        apply integral_congr_ae
        filter_upwards [he] with x hx
        rw [←l2_set_integral_eq_inner ν B hB hf.ne]
        exact integral_congr_ae (ae_restrict_of_ae hx)
      _ = _ := integral_integral_swap (hp B hB hf)
/-- On a probability space, integrable L2-valued realizations are jointly
integrable; hence their parameter integrals exist almost surely. -/
theorem l2_realizations_product_integrable {E S:Type*} [MeasurableSpace E] [MeasurableSpace S]
    (μ:Measure E) [SigmaFinite μ] (ν:Measure S) [IsProbabilityMeasure ν]
    (H:E × S → ℝ) (hm:Measurable H) (Z:E → Lp ℝ 2 ν) (hi:Integrable Z μ)
    (he:∀ᵐx∂μ,(Z x:S → ℝ)=ᵐ[ν] (fun s => H (x,s))) :
    Integrable H (μ.prod ν) := by
  have hp (B:Set S) (hB:MeasurableSet B) (hf:ν B<∞):Integrable H (μ.prod (ν.restrict B)) := by
    letI:IsFiniteMeasure (ν.restrict B):=⟨by simpa using hf⟩
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [he] with x hx
      exact (((MeasureTheory.Lp.memLp (Z x)).ae_eq hx).restrict B).integrable (by norm_num)
    · apply (hi.norm.const_mul ‖indicatorConstLp 2 hB hf.ne (1:ℝ)‖).mono'
        (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      filter_upwards [he] with x hx
      have hl:MemLp (fun s => H (x,s)) 2 ν := (MeasureTheory.Lp.memLp (Z x)).ae_eq hx
      have hz:hl.toLp (fun s => H (x,s))=Z x := by
        apply Lp.ext
        exact hl.coeFn_toLp.trans hx.symm
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      simpa only [hz] using l2_set_integral_norm_bound ν B hB hf.ne _ hl
  simpa only [Measure.restrict_univ] using hp univ MeasurableSet.univ (by simp)

end Asakura.Chapter13
#print axioms Asakura.Chapter13.l2_bochner_pointwise_ae

#print axioms Asakura.Chapter13.l2_realizations_product_integrable
