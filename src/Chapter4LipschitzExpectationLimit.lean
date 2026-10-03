import Chapter4BoundedConditionalLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1600000

lemma lipschitz_expectation_L2_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → E) (Y : Ω → E)
    (hXm : ∀ n,Measurable (X n)) (hYm : Measurable Y)
    (hXi : ∀ n,MemLp (X n) 2 P) (hYi : MemLp Y 2 P)
    (ht : Tendsto (fun n => ∫ w,‖X n w-Y w‖^2 ∂P) atTop (𝓝 0))
    (f : E → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    Tendsto (fun n => ∫ w,f (X n w) ∂P) atTop (𝓝 (∫ w,f (Y w) ∂P)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => lipschitz_expectation_difference_le P (X n) Y (hXm n) hYm (hXi n) hYi f L hL B hb)
  simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp ht).const_mul (L:ℝ)

end Asakura.Chapter4
