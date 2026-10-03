import Chapter2SignedCumulativeContinuity

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem right_continuous_cumulative_integral
    (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Integrable f μ) (t : ℝ) :
    ContinuousWithinAt (fun s => ∫ r in Iic s, f r ∂μ) (Ici t) t := by
  have he s : (∫ r in Iic s, f r ∂μ) = ∫ r, (Iic s).indicator f r ∂μ :=
    (integral_indicator measurableSet_Iic).symm
  simp only [he]
  refine continuousWithinAt_of_dominated (bound := fun r => ‖f r‖)
    (Filter.Eventually.of_forall (fun s => hf.aestronglyMeasurable.indicator measurableSet_Iic)) ?_ hf.norm ?_
  · exact Filter.Eventually.of_forall (fun s => ae_of_all _ (fun r => by
      by_cases hr : r ∈ Iic s <;> simp [indicator,hr]))
  · exact ae_of_all _ (fun r => by
      change Tendsto (fun s => (Iic s).indicator f r) (𝓝[Ici t] t) (𝓝 ((Iic t).indicator f r))
      by_cases hr : r ≤ t
      · rw [indicator_of_mem (show r ∈ Iic t from hr)]
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (indicator_of_mem (show r ∈ Iic s from hr.trans hs) f).symm
      · rw [indicator_of_notMem (show r ∉ Iic t from hr)]
        apply tendsto_const_nhds.congr'
        filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (lt_of_not_ge hr))] with s hs
        exact (indicator_of_notMem (show r ∉ Iic s from not_le_of_gt hs) f).symm)

/-- Right continuity requires no atomlessness. Thus this part applies to
the chapter's right-continuous finite-variation integrators with jumps. -/
theorem signed_cumulative_right_continuous
    (ν : SignedMeasure ℝ) (f : ℝ → ℝ) (hf : Integrable f ν.totalVariation) (t : ℝ) :
    ContinuousWithinAt (signedCumulative ν f) (Ici t) t := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  have h := (right_continuous_cumulative_integral _ f (hf.mono_measure hp) t).sub
    (right_continuous_cumulative_integral _ f (hf.mono_measure hn) t)
  change ContinuousWithinAt (fun s => (∫ r, (Iic s).indicator f r ∂ν.toJordanDecomposition.posPart)-
    (∫ r, (Iic s).indicator f r ∂ν.toJordanDecomposition.negPart)) (Ici t) t
  simp_rw [integral_indicator measurableSet_Iic]
  exact h

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_cumulative_right_continuous
