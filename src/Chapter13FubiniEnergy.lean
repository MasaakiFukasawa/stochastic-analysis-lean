import Chapter2FiniteHorizonEnergy
import Chapter8RandomIntegralSquare

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter13
open Asakura.Chapter2Complete Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A finite parameter measure and total square energy imply the exact mixed
L1(L2) condition used in stochastic Fubini. -/
theorem finite_parameter_fubini_energy {E S:Type*} [MeasurableSpace E] [MeasurableSpace S]
    (μ:Measure E) [IsFiniteMeasure μ] (ν:Measure S) [SigmaFinite ν]
    (H:E × S → ℝ) (hH:Measurable H) (hi:Integrable (fun z => H z^2) (μ.prod ν)) :
    (∫⁻x,eLpNorm (fun z => H (x,z)) 2 ν∂μ)<∞ ∧
    (∫x,Real.sqrt (∫z,H (x,z)^2∂ν)∂μ)^2≤μ.real univ*(∫z,H z^2∂(μ.prod ν)) := by
  let e:=fun x => ∫z,H (x,z)^2∂ν
  have hm:Measurable e := ((hH.pow_const 2).stronglyMeasurable.integral_prod_right).measurable
  have he:Integrable e μ := hi.integral_prod_left
  have hep x:0≤e x := integral_nonneg (fun _ => sq_nonneg _)
  have hs:MemLp (fun x => Real.sqrt (e x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hm.sqrt.aestronglyMeasurable).mpr
    simpa only [Real.sq_sqrt (hep _)] using he
  have hnorm:(fun x => eLpNorm (fun z => H (x,z)) 2 ν)=ᵐ[μ] (fun x => ENNReal.ofReal (Real.sqrt (e x))) := by
    filter_upwards [hi.prod_right_ae] with x hx
    have hL:MemLp (fun z => H (x,z)) 2 ν :=
      (memLp_two_iff_integrable_sq (hH.comp measurable_prodMk_left).aestronglyMeasurable).mpr hx
    rw [real_eLpNorm_two_energy ν _ hL]
    dsimp only [e]
    rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (by norm_num)]
    rw [Real.sqrt_eq_rpow]
  have hsi:=hs.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  refine ⟨?_,?_⟩
  · rw [lintegral_congr_ae hnorm,←ofReal_integral_eq_lintegral_ofReal hsi (ae_of_all _ (fun _ => Real.sqrt_nonneg _))]
    exact ENNReal.ofReal_lt_top
  · have hh:=finite_measure_integral_square μ (fun x => Real.sqrt (e x)) hs
    simp only [Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hep _)] at hh
    simpa only [e,←integral_prod _ hi] using hh
end Asakura.Chapter13
#print axioms Asakura.Chapter13.finite_parameter_fubini_energy
