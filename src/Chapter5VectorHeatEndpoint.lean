import Chapter5HeatFDeriv

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000

/-- At-most-linear growth suffices for the heat average in any dimension. -/
theorem vector_lipschitz_average_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (C : ℝ≥0) (hf : LipschitzWith C f) (x : E) (t : ℝ) :
    Integrable (fun z => f (x+Real.sqrt t • z)) ν := by
  apply ((integrable_const ‖f x‖).add (hi.norm.const_mul ((C:ℝ)*Real.sqrt t))).mono'
    (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  apply ae_of_all
  intro z
  have hh := hf.dist_le_mul (x+Real.sqrt t • z) x
  simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t)] at hh
  calc
    ‖f (x+Real.sqrt t • z)‖ ≤ ‖f x‖+‖f (x+Real.sqrt t • z)-f x‖ := by
      simpa only [add_sub_cancel] using norm_add_le (f x) (f (x+Real.sqrt t • z)-f x)
    _ ≤ ‖f x‖+(C:ℝ)*Real.sqrt t*‖z‖ := by
      simpa only [Real.norm_eq_abs,mul_assoc,add_comm] using add_le_add_left hh ‖f x‖

/-- The endpoint estimate allows the space variable to vary and does
not assume that the terminal function itself is bounded. -/
theorem vector_heat_endpoint_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hi : Integrable (fun z : E => z) ν)
    (f : E → ℝ) (C : ℝ≥0) (hf : LipschitzWith C f) (x y : E) (t : ℝ) :
    |(∫ z,f (x+Real.sqrt t • z) ∂ν)-f y| ≤
      (C:ℝ)*(‖x-y‖+Real.sqrt t*(∫ z,‖z‖ ∂ν)) := by
  have hfi := vector_lipschitz_average_integrable ν hi f C hf x t
  have he : (∫ z,f (x+Real.sqrt t • z) ∂ν)-f y = ∫ z,f (x+Real.sqrt t • z)-f y ∂ν := by
    rw [integral_sub hfi (integrable_const _)]; simp
  rw [he]
  calc
    _ ≤ ∫ z,‖f (x+Real.sqrt t • z)-f y‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ z,(C:ℝ)*(‖x-y‖+Real.sqrt t*‖z‖) ∂ν := by
      apply integral_mono (hfi.sub (integrable_const _)).norm
        (((integrable_const _).add (hi.norm.const_mul _)).const_mul _)
      intro z
      dsimp only [Pi.add_apply]
      have hh := hf.dist_le_mul (x+Real.sqrt t • z) y
      simp only [dist_eq_norm] at hh
      refine hh.trans (mul_le_mul_of_nonneg_left ?_ C.coe_nonneg)
      have he' : x+Real.sqrt t • z-y = (x-y)+Real.sqrt t • z := by abel
      rw [he']
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg t)] using norm_add_le (x-y) (Real.sqrt t • z)
    _ = _ := by
      rw [integral_const_mul,integral_add (integrable_const _) (hi.norm.const_mul _),integral_const_mul]
      simp

end Asakura.Chapter5
