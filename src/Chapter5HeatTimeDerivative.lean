import Chapter5HeatFDeriv

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2400000

/-- Differentiate the genuine vector Gaussian average in time. The
integrable dominating function is a constant times the norm of the
Gaussian vector, uniformly on a neighborhood of the positive time. -/
theorem vector_average_time_derivative_of_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (C : ℝ) (hDb : ∀ x,‖D x‖ ≤ C)
    (x : E) (t : ℝ) (ht : 0 < t)
    (hfi : Integrable (fun z => f (x+Real.sqrt t • z)) ν) :
    HasDerivAt (fun s => ∫ z,f (x+Real.sqrt s • z) ∂ν)
      (∫ z,D (x+Real.sqrt t • z) z/(2*Real.sqrt t) ∂ν) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have hC : 0 ≤ C := (norm_nonneg (D x)).trans (hDb x)
  have hs : 0 < Real.sqrt (t/2) := Real.sqrt_pos.mpr (by positivity)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (s := Ioi (t/2)) (bound := fun z => C*‖z‖/(2*Real.sqrt (t/2)))
    (F' := fun u z => D (x+Real.sqrt u • z) z/(2*Real.sqrt u))
    (Ioi_mem_nhds (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun u => (hfc.comp (by fun_prop)).aestronglyMeasurable
  · exact hfi
  · exact (((hDc.comp (by fun_prop)).clm_apply continuous_id).div_const _).aestronglyMeasurable
  · apply ae_of_all
    intro z u hu
    have hu0 : 0 < u := lt_trans (by linarith : 0 < t/2) hu
    rw [norm_div,Real.norm_eq_abs (2*Real.sqrt u),abs_of_pos (by positivity : 0 < 2*Real.sqrt u)]
    calc
      _ ≤ C*‖z‖/(2*Real.sqrt u) := div_le_div_of_nonneg_right
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hDb _) (norm_nonneg z))) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC (norm_nonneg z)) (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu.le) (by norm_num))
  · exact (hi.norm.const_mul C).div_const _
  · apply ae_of_all
    intro z u hu
    have hu0 : 0 < u := lt_trans (by linarith : 0 < t/2) hu
    have hh := (hd (x+Real.sqrt u • z)).comp_hasDerivAt u
      (((Real.hasDerivAt_sqrt hu0.ne').smul_const z).const_add x)
    convert hh using 1
    all_goals simp [Function.comp_def,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem vector_average_time_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hd : ∀ x,HasFDerivAt f (D x) x) (hDc : Continuous D)
    (B C : ℝ) (hb : ∀ x,‖f x‖ ≤ B) (hDb : ∀ x,‖D x‖ ≤ C)
    (x : E) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ z,f (x+Real.sqrt s • z) ∂ν)
      (∫ z,D (x+Real.sqrt t • z) z/(2*Real.sqrt t) ∂ν) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  exact vector_average_time_derivative_of_integrable ν hi f D hd hDc C hDb x t ht
    (Integrable.of_bound (hfc.comp (by fun_prop)).aestronglyMeasurable B (ae_of_all _ fun z => hb _))

end Asakura.Chapter5
