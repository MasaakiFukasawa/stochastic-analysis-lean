import Chapter11PayoffHeatSmooth
import Chapter11PayoffIntegrability

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace Asakura.Chapter11
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem heat_log_kernel_pdf (t y z : ℝ) (ht : 0<t) :
    heatLogKernel z (t,y)=gaussianPDFReal y (NNReal.mk t ht.le) z := by
  have hp : 0<2*Real.pi*t := by positivity
  have he : Real.exp (-(1:ℝ)/2*Real.log (2*Real.pi*t))=(Real.sqrt (2*Real.pi*t))⁻¹ := by
    rw [←Real.exp_log (Real.sqrt_pos.2 hp),←Real.exp_neg,Real.log_sqrt hp.le]
    congr 1
    ring
  dsimp only [heatLogKernel,gaussianPDFReal,NNReal.coe_mk]
  rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,he]
  congr 2
  ring

theorem heat_gaussian_representation (f : ℝ → ℝ) (hf : Measurable f)
    (t y : ℝ) (ht : 0<t) :
    (∫ z,f z*heatLogKernel z (t,y))=(∫ z,f (y+Real.sqrt t*z) ∂gaussianReal 0 1) := by
  have hv : ((NNReal.mk t ht.le) : ℝ≥0)≠0 := by intro h;have hh := congrArg (fun a : ℝ≥0 => (a:ℝ)) h;exact ht.ne' hh
  have he : (∫ z,f z*heatLogKernel z (t,y))=(∫ z,f z ∂gaussianReal y (NNReal.mk t ht.le)) := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change f z*heatLogKernel z (t,y)=gaussianPDFReal y (NNReal.mk t ht.le) z • f z
      rw [heat_log_kernel_pdf t y z ht,smul_eq_mul,mul_comm]
  rw [he]
  have hs : (gaussianReal 0 1).map (fun z => Real.sqrt t*z)=gaussianReal 0 (NNReal.mk t ht.le) := by
    have hh := gaussianReal_map_const_mul (μ:=0) (v:=1) (Real.sqrt t)
    simpa only [mul_zero,mul_one,Real.sq_sqrt ht.le] using hh
  have hm : (gaussianReal 0 1).map (fun z => y+Real.sqrt t*z)=gaussianReal y (NNReal.mk t ht.le) := by
    rw [show (fun z => y+Real.sqrt t*z)=(fun a => y+a) ∘ (fun z => Real.sqrt t*z) from rfl,
      ←Measure.map_map (by fun_prop) (by fun_prop),hs]
    simpa using gaussianReal_map_const_add (μ:=0) (v:=(NNReal.mk t ht.le)) y
  rw [←hm]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

end Asakura.Chapter11
