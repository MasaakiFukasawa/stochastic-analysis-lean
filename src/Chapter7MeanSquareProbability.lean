import Chapter2EnergyNorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false

lemma mean_square_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hi : ∀ n,MemLp (fun w => X n w-Y w) 2 P)
    (he : Tendsto (fun n => ∫ w,(X n w-Y w)^2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P X atTop Y := by
  have ho := ENNReal.continuous_ofReal.continuousAt.tendsto.comp he
  have hr := (ENNReal.continuous_rpow_const (y := 1/(2:ℝ))).continuousAt.tendsto.comp ho
  simp only [Function.comp_def,ENNReal.ofReal_zero,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ)<1/2)] at hr
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  have hn n := real_eLpNorm_two_energy P (X n-Y) (hi n)
  simpa only [hn,Pi.sub_apply] using hr

/-- Bias and variance estimates suffice for the bracket limit. Both estimates
will be derived for the interval integrals in the estimator construction. -/
lemma mean_square_from_bias_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : MemLp X 2 P)
    (c : ℝ) :
    (∫ w,(X w-c)^2 ∂P)=(∫ w,(X w-(∫ v,X v ∂P))^2 ∂P)+((∫ w,X w ∂P)-c)^2 := by
  let a := ∫ w,X w ∂P
  have hi : Integrable X P := hX.integrable (by norm_num)
  have his : Integrable (fun w => X w^2) P := (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mp hX
  have formula (b : ℝ) : (∫ w,(X w-b)^2 ∂P)=(∫ w,X w^2 ∂P)-2*b*a+b^2 := by
    have he w : (X w-b)^2=X w^2-2*b*X w+b^2 := by ring
    simp_rw [he]
    have him : Integrable (fun w => 2*b*X w) P := hi.const_mul _
    have hisub : Integrable (fun w => X w^2-2*b*X w) P := his.sub him
    rw [integral_add hisub (integrable_const _),integral_sub his him,integral_const_mul]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,a]
  rw [formula c,formula a]
  dsimp only [a]
  ring

end Asakura.Chapter7
