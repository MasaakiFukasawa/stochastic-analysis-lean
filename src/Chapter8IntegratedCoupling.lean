import Chapter8WeightedCoupling
import Chapter8StationaryIntegralL1
import FullAuditTimeAverageCoupling

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- Integrate the exponentially decaying expected coupling error; all
product integrability needed for Fubini is derived from that bound. -/
theorem integrated_coupling_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry R)) (hi : ∀ t≥0,Integrable (fun w => R w t) P)
    (C κ T : ℝ) (hC : 0≤C) (hκ : 0<κ) (hT : 0<T)
    (hb : ∀ t≥0,(∫ w,|R w t| ∂P)≤C*Real.exp (-κ*t)) :
    Integrable (fun w => timeAverage (R w) T) P ∧
      (∫ w,|timeAverage (R w) T| ∂P)≤C/(κ*T) := by
  let ν := volume.restrict (Ioc (0:ℝ) T)
  have hprod : Integrable (Function.uncurry R) (P.prod ν) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hi t ht.1.le
    · apply (integrable_const C).mono' (hm.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have he : Real.exp (-κ*t)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
      change ‖∫ w,‖R w t‖ ∂P‖ ≤ C
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ ∫ w,‖R w t‖ ∂P from
        integral_nonneg (fun w => norm_nonneg (R w t)))]
      simpa only [Real.norm_eq_abs] using
        (hb t ht.1.le).trans (mul_le_of_le_one_right hC he)
  have hbound : (∫ w,|∫ t,R w t ∂ν| ∂P)≤C/κ := by
    have hh := integral_mono hprod.integral_prod_left.norm hprod.norm.integral_prod_left
      (fun w => norm_integral_le_integral_norm (R w))
    rw [integral_integral_swap hprod.norm] at hh
    have hE : Integrable (fun t => C*Real.exp (-κ*t)) ν :=
      ((by fun_prop : Continuous (fun t : ℝ => C*Real.exp (-κ*t))).intervalIntegrable 0 T).1
    have hh2 := integral_mono_ae hprod.norm.integral_prod_right hE (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simpa only [Real.norm_eq_abs,Function.uncurry_def] using hb t ht.1.le)
    have he : (∫ t,C*Real.exp (-κ*t) ∂ν)≤C/κ := by
      change (∫ t in Ioc (0:ℝ) T,C*Real.exp (-κ*t))≤C/κ
      rw [← intervalIntegral.integral_of_le hT.le,intervalIntegral.integral_const_mul,
        integrated_exponential_decay κ T hκ]
      have hh := mul_le_mul_of_nonneg_left (show 1-Real.exp (-κ*T)≤1 from by linarith [Real.exp_pos (-κ*T)]) hC
      apply (le_div_iff₀ hκ).mpr
      convert hh using 1 <;> field_simp
    exact (show (∫ w,|∫ t,R w t ∂ν| ∂P)≤∫ t,(∫ w,‖R w t‖ ∂P) ∂ν from by
      simpa only [Real.norm_eq_abs,Function.uncurry_def] using hh).trans (hh2.trans he)
  constructor
  · simpa only [timeAverage,intervalIntegral.integral_of_le hT.le,Function.uncurry_def,ν] using
      hprod.integral_prod_left.const_mul T⁻¹
  · simp only [timeAverage,intervalIntegral.integral_of_le hT.le,abs_mul,abs_of_pos (inv_pos.mpr hT)]
    rw [integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hT.le)
    convert hh using 1 <;> ring

end Asakura.Chapter8
