import Chapter1StieltjesPartitionConvergence

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace Asakura.Chapter1Complete
set_option maxHeartbeats 2000000

lemma discrete_variation_continuous (a b : ℝ) (C : ℝ → ℝ)
    (hC : ContinuousOn C (Icc a b)) (π : IntervalCells a b) :
    ContinuousOn (intervalDiscreteVariation C π) (Icc a b) := by
  apply continuousOn_finsetSum
  intro E hE
  have hb := π.bounds E hE
  apply ContinuousOn.abs
  apply ContinuousOn.sub
  · exact hC.comp (continuous_const.min continuous_id).continuousOn
      (fun t ht => ⟨le_min (hb.1.trans hb.2.1) ht.1,(min_le_left _ _).trans hb.2.2⟩)
  · exact hC.comp (continuous_const.min continuous_id).continuousOn
      (fun t ht => ⟨le_min hb.1 ht.1,(min_le_left _ _).trans (hb.2.1.trans hb.2.2)⟩)

lemma continuous_cumulative_variation (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b)) (hc : ContinuousOn C (Icc a b)) :
    ContinuousOn (fun t => (eVariationOn C (Icc a t)).toReal) (Icc a b) := by
  have h : ContinuousOn (variationOnFromTo C (Icc a b) a) (Icc a b) :=
    fun x hx => (hC.continuousWithinAt_variationOnFromTo_iff (left_mem_Icc.mpr hab) hx).mpr (hc x hx)
  apply h.congr
  intro t ht
  rw [variationOnFromTo.eq_of_le C (Icc a b) ht.1]
  rw [inter_eq_right.mpr (Icc_subset_Icc le_rfl ht.2)]

/-- Compactness upgrades the pointwise monotone convergence to uniform
convergence, using continuity of C and its cumulative total variation. -/
theorem stieltjes_partition_uniform_convergence (a b : ℝ) (hab : a≤b) (C : ℝ → ℝ)
    (hC : BoundedVariationOn C (Icc a b)) (hc : ContinuousOn C (Icc a b))
    (π : ℕ → IntervalCells a b) (href : Antitone (fun n => (π n).partition))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ n,∀ E∈(π n).partition.parts,(π n).right E-(π n).left E≤δ n) :
    TendstoUniformlyOn (fun n => intervalDiscreteVariation C (π n))
      (fun t => (eVariationOn C (Icc a t)).toReal) atTop (Icc a b) := by
  have hr x (hx : x∈Icc a b) : ContinuousWithinAt C (Icc a b∩Ici x) x :=
    (hc x hx).mono inter_subset_left
  have h t (ht : t∈Icc a b) := stieltjes_partition_convergence a b hab C hC hr π href δ hδ hmesh ht
  exact Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (fun n => discrete_variation_continuous a b C hc (π n))
    (fun t ht => (h t ht).1) (continuous_cumulative_variation a b hab C hC hc)
    (fun t ht => (h t ht).2)

end Asakura.Chapter1Complete
