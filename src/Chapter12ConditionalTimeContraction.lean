import FullAuditJensenContraction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The integrated conditional Jensen estimate used when passing from
cylinders to the closed Malliavin derivative. Joint L2 membership is proved,
not inferred merely from separate-time square integrability. -/
theorem conditional_time_L2_contraction {Ω S : Type*} [m : MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure S) [SigmaFinite ν] (F : S → MeasurableSpace Ω) (hle : ∀ t,F t ≤ m)
    (u q : Ω × S → ℝ) (hum : Measurable u) (hqm : Measurable q)
    (hu : MemLp u 2 (P.prod ν))
    (he : ∀ᵐ t ∂ν,(fun w => q (w,t)) =ᵐ[P] P[(fun w => u (w,t))|F t]) :
    MemLp q 2 (P.prod ν) ∧ (∫ z,q z^2 ∂P.prod ν) ≤ ∫ z,u z^2 ∂P.prod ν := by
  have huisq := hu.integrable_sq
  have hmoment : ∀ᵐ t ∂ν,Integrable (fun w => q (w,t)^2) P ∧
      (∫ w,q (w,t)^2 ∂P) ≤ ∫ w,u (w,t)^2 ∂P := by
    filter_upwards [he,huisq.prod_left_ae] with t ht hut
    have hu2 : MemLp (fun w => u (w,t)) 2 P :=
      (memLp_two_iff_integrable_sq (hum.comp measurable_prodMk_right).aestronglyMeasurable).mpr hut
    have hc := conditional_norm_power_written P (hle t) 2 (by norm_num) (by norm_num)
      (fun w => u (w,t)) hu2
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] at hc
    have hes : (fun w => q (w,t)^2) =ᵐ[P] (fun w => P[(fun w => u (w,t))|F t] w^2) :=
      ht.mono (fun w hw => congrArg (fun x : ℝ => x^2) hw)
    exact ⟨hc.1.congr hes.symm,(integral_congr_ae hes).le.trans hc.2⟩
  have hqi : Integrable (fun z => q z^2) (P.prod ν) := by
    apply (integrable_prod_iff' (hqm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨hmoment.mono fun t ht => ht.1,?_⟩
    have hm := ((hqm.pow_const 2).norm.stronglyMeasurable.integral_prod_left' (μ := P))
    apply huisq.integral_prod_right.mono' hm.aestronglyMeasurable
    filter_upwards [hmoment] with t ht
    simp only [Real.norm_eq_abs,abs_sq]
    rw [abs_of_nonneg (integral_nonneg fun w => sq_nonneg (q (w,t)))]
    exact ht.2
  refine ⟨(memLp_two_iff_integrable_sq hqm.aestronglyMeasurable).mpr hqi,?_⟩
  rw [integral_prod_symm _ hqi,integral_prod_symm _ huisq]
  exact integral_mono_ae hqi.integral_prod_right huisq.integral_prod_right
    (hmoment.mono fun t ht => ht.2)

end Asakura.Chapter12
