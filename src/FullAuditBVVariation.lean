import FullAuditStieltjesIntervals
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Measure.Stieltjes

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- The interval partition has exactly the total mass of its union, including
repeated endpoints and the empty partition. -/
theorem measure_interval_partition (μ : Measure ℝ) (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, μ (Ioc (u i) (u (i+1))) = μ (Ioc (u 0) (u n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,← measure_union]
    · rw [Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]
    · apply Set.disjoint_left.mpr
      intro x hx hy
      exact not_lt_of_ge hx.2 hy.1
    · exact measurableSet_Ioc

/-- Finite interval partitions in the definition of BV are bounded by the
variation of any signed measure with the prescribed interval increments. -/
theorem interval_variation_le_signed_variation (C : ℝ → ℝ) (ν : SignedMeasure ℝ)
    (hν : ∀ s t, s ≤ t → ν (Ioc s t) = C t-C s) (s t : ℝ) :
    eVariationOn C (Icc s t) ≤ ν.totalVariation (Ioc s t) := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, ν.totalVariation (Ioc (u i) (u (i+1))) := by
      apply Finset.sum_le_sum
      intro i _
      have h := ν.enorm_le_totalVariation (Ioc (u i) (u (i+1)))
      rw [hν _ _ (hu (Nat.le_succ i))] at h
      simpa only [edist_eq_enorm_sub] using h
    _ = ν.totalVariation (Ioc (u 0) (u n)) := measure_interval_partition _ u hu n
    _ ≤ _ := measure_mono (Ioc_subset_Ioc (hus 0).1 (hus n).2)

/-- The variation function inherits right continuity from the original BV
function; these are the exact ingredients used to construct dC. -/
noncomputable def bvVariation (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) : StieltjesFunction ℝ where
  toFun := variationOnFromTo C univ a
  mono' := fun _ _ h => variationOnFromTo.monotoneOn hC.locallyBoundedVariationOn (mem_univ a) (mem_univ _) (mem_univ _) h
  right_continuous' x := hC.continuousWithinAt_variationOnFromTo_Ici (hr x)

noncomputable def bvPositive (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) : StieltjesFunction ℝ where
  toFun x := (variationOnFromTo C univ a x+(C x-C a))/2
  mono' := by
    intro x y hxy
    have h := variationOnFromTo.add_self_monotoneOn hC.locallyBoundedVariationOn (mem_univ a) (mem_univ x) (mem_univ y) hxy
    simp only [Pi.add_apply] at h
    linarith
  right_continuous' x := ((hC.continuousWithinAt_variationOnFromTo_Ici (hr x)).add ((hr x).sub continuousWithinAt_const)).div_const 2

noncomputable def bvNegative (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) : StieltjesFunction ℝ where
  toFun x := (variationOnFromTo C univ a x-(C x-C a))/2
  mono' := by
    intro x y hxy
    have h := variationOnFromTo.sub_self_monotoneOn hC.locallyBoundedVariationOn (mem_univ a) (mem_univ x) (mem_univ y) hxy
    simp only [Pi.sub_apply] at h
    linarith
  right_continuous' x := ((hC.continuousWithinAt_variationOnFromTo_Ici (hr x)).sub ((hr x).sub continuousWithinAt_const)).div_const 2

theorem bv_variation_finite (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) :
    IsFiniteMeasure (bvVariation C hC hr a).measure :=
  (bvVariation C hC hr a).isFiniteMeasure_of_forall_abs_le fun x => variationOnFromTo.abs_le_eVariationOn hC

theorem bv_parts_finite (C : ℝ → ℝ) (hC : BoundedVariationOn C univ)
    (hr : ∀ x, ContinuousWithinAt C (Ici x) x) (a : ℝ) :
    IsFiniteMeasure (bvPositive C hC hr a).measure ∧ IsFiniteMeasure (bvNegative C hC hr a).measure := by
  have hbound : ∀ x, |variationOnFromTo C univ a x|+|C x-C a| ≤ 2*(eVariationOn C univ).toReal := by
    intro x
    have hv := variationOnFromTo.abs_le_eVariationOn (a := a) (b := x) hC
    have hc := hC.dist_le (mem_univ x) (mem_univ a)
    rw [Real.dist_eq] at hc
    linarith
  constructor
  · apply (bvPositive C hC hr a).isFiniteMeasure_of_forall_abs_le (C := (eVariationOn C univ).toReal)
    intro x
    change |(variationOnFromTo C univ a x+(C x-C a))/2| ≤ _
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr ((abs_add_le _ _).trans (by linarith [hbound x]))
  · apply (bvNegative C hC hr a).isFiniteMeasure_of_forall_abs_le (C := (eVariationOn C univ).toReal)
    intro x
    change |(variationOnFromTo C univ a x-(C x-C a))/2| ≤ _
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    have h := abs_sub_le (variationOnFromTo C univ a x) 0 (C x-C a)
    simp only [sub_zero,zero_sub,abs_neg] at h
    exact h.trans (by linarith [hbound x])

end Asakura.FullAudit
