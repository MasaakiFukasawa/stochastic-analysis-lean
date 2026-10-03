import Chapter6SquareMeanToL1

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 1600000

theorem finite_sum_L1_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ℕ → ι → Ω → ℝ)
    (hi : ∀ n i,Integrable (X n i) P)
    (hl : ∀ i,Tendsto (fun n => ∫ w,|X n i w| ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ w,|∑ i,X n i w| ∂P) atTop (𝓝 0) := by
  have hb n : (∫ w,|∑ i,X n i w| ∂P)≤∑ i,∫ w,|X n i w| ∂P := by
    rw [←integral_finsetSum _ (fun i _ => (hi n i).abs)]
    exact integral_mono (integrable_finsetSum _ (fun i _ => hi n i)).abs
      (integrable_finsetSum _ (fun i _ => (hi n i).abs)) (fun w => Finset.abs_sum_le_sum_abs _ _)
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) hb
  simpa using tendsto_finset_sum univ (fun i _ => hl i)

end Asakura.Chapter6
