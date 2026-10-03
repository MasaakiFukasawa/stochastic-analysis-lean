import Chapter6GaussianBridgeResidual

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6

theorem square_mean_zero_implies_L1_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n,MemLp (X n) 2 P)
    (hl : Tendsto (fun n => ∫ w,X n w^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ w,|X n w| ∂P) atTop (𝓝 0) := by
  have hb n : (∫ w,|X n w| ∂P)≤Real.sqrt (∫ w,X n w^2 ∂P) := by
    simpa only [sq_abs] using integral_le_sqrt_second_moment P (fun w => |X n w|) (hX n).abs
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) hb
  simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hl

end Asakura.Chapter6
