import Chapter5GeneratorL2
import Chapter2M2TerminalRealization
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The chapter's sample-time L² assumption supplies both pathwise L²
and integrable expected energy; these are conclusions of Fubini. -/
theorem finite_time_L2_sections
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (hi : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    (∀ᵐ w ∂P, MemLp (fun r => H (w,r)) 2 (volume.restrict (Ioc 0 R))) ∧
    Integrable (fun w => ∫ r in 0..R,H (w,r)^2) P := by
  have hsq := (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mp hi
  constructor
  · filter_upwards [hsq.prod_right_ae] with w hw
    exact (memLp_two_iff_integrable_sq (hH.comp measurable_prodMk_left).aestronglyMeasurable).mpr hw
  · simpa only [intervalIntegral.integral_of_le hR] using hsq.integral_prod_left

/-- Finite exponential weights preserve the L² energy assumption and
justify all expectation/time-integral interchanges in the estimate. -/
theorem finite_time_weighted_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (β : ℝ) (hβ : 0 ≤ β)
    (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (hi : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R)))) :
    Integrable (fun z => Real.exp (β*z.2)*H z^2) (P.prod (volume.restrict (Ioc 0 R))) ∧
    (∀ᵐ w ∂P, IntervalIntegrable (fun r => Real.exp (β*r)*H (w,r)^2) volume 0 R) ∧
    Integrable (fun w => ∫ r in 0..R,Real.exp (β*r)*H (w,r)^2) P ∧
    (∫ w, (∫ r in 0..R,Real.exp (β*r)*H (w,r)^2) ∂P) =
      ∫ r in 0..R, ∫ w, Real.exp (β*r)*H (w,r)^2 ∂P := by
  have hsq := (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mp hi
  have hs : ∀ᵐ z ∂P.prod (volume.restrict (Ioc 0 R)), z.2 ∈ Ioc 0 R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
    exact ae_of_all _ fun w => ae_restrict_mem measurableSet_Ioc
  have hm : Measurable (fun z : Ω × ℝ => Real.exp (β*z.2)*H z^2) :=
    ((measurable_const.mul measurable_snd).exp).mul (hH.pow_const 2)
  have hw : Integrable (fun z : Ω × ℝ => Real.exp (β*z.2)*H z^2) (P.prod (volume.restrict (Ioc 0 R))) := by
    apply (hsq.const_mul (Real.exp (β*R))).mono' hm.aestronglyMeasurable
    filter_upwards [hs] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz.2 hβ)) (sq_nonneg _)
  refine ⟨hw,?_,?_,?_⟩
  · filter_upwards [hw.prod_right_ae] with w hww
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr hww
  · simpa only [intervalIntegral.integral_of_le hR] using hw.integral_prod_left
  · simpa only [intervalIntegral.integral_of_le hR] using integral_integral_swap hw

/-- The same integrability conclusions hold on every tail interval. -/
theorem finite_time_weighted_tail_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ) (hR : 0 ≤ R) (β : ℝ) (hβ : 0 ≤ β)
    (H : Ω × ℝ → ℝ) (hH : Measurable H)
    (hi : MemLp H 2 (P.prod (volume.restrict (Ioc 0 R))))
    (t : ℝ) (ht : t ∈ Icc 0 R) :
    (∀ᵐ w ∂P, IntervalIntegrable (fun r => Real.exp (β*r)*H (w,r)^2) volume t R) ∧
    Integrable (fun w => ∫ r in t..R,Real.exp (β*r)*H (w,r)^2) P := by
  have hw := (finite_time_weighted_energy P R hR β hβ H hH hi).1
  have hwt : Integrable (fun z => Real.exp (β*z.2)*H z^2) (P.prod (volume.restrict (Ioc t R))) :=
    hw.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono (Ioc_subset_Ioc_left ht.1) le_rfl))
  constructor
  · filter_upwards [hwt.prod_right_ae] with w hw
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2).mpr hw
  · simpa only [intervalIntegral.integral_of_le ht.2] using hwt.integral_prod_left

end Asakura.Chapter5
