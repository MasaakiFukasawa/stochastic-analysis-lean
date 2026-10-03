import Chapter2SignedIntegralContinuity
import Chapter2CumulativeIntegral
import FullAuditBVVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable def signedCumulative (ν : SignedMeasure ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  signedIntegralRaw ν ((Iic t).indicator f)

theorem signed_cumulative_increment (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν.totalVariation) (s t : ℝ) (hst : s ≤ t) :
    signedCumulative ν f t-signedCumulative ν f s = signedIntegralRaw ν ((Ioc s t).indicator f) := by
  rw [signedCumulative,signedCumulative,← signed_integral_sub ν _ _
    (hf.indicator measurableSet_Iic) (hf.indicator measurableSet_Iic)]
  congr 1
  funext r
  by_cases hrs : r ≤ s
  · simp [Set.indicator,hrs,hrs.trans hst]
  · by_cases hrt : r ≤ t <;> simp [Set.indicator,hrs,hrt]

/-- Partition variation is bounded by any positive measure dominating all
interval increments. This is the deterministic core of exercise rep252(4). -/
theorem interval_variation_le_increment_measure (C : ℝ → ℝ) (μ : Measure ℝ)
    (hμ : ∀ s t, s ≤ t → ENNReal.ofReal |C t-C s| ≤ μ (Ioc s t)) (a b : ℝ) :
    eVariationOn C (Icc a b) ≤ μ (Ioc a b) := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n,u,hu,hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, μ (Ioc (u i) (u (i+1))) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [edist_dist,Real.dist_eq] using hμ (u i) (u (i+1)) (hu (Nat.le_succ i))
    _ = μ (Ioc (u 0) (u n)) := measure_interval_partition μ u hu n
    _ ≤ _ := measure_mono (Ioc_subset_Ioc (hus 0).1 (hus n).2)

/-- The variation bound is proved for the actual signed Stieltjes integral,
using Jordan integration and the supremum over finite interval partitions. -/
theorem signed_cumulative_variation_bound (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν.totalVariation) (a b : ℝ) :
    eVariationOn (signedCumulative ν f) (Icc a b) ≤
      ENNReal.ofReal (∫ r in Ioc a b, |f r| ∂ν.totalVariation) := by
  let μ := ν.totalVariation.withDensity (fun r => ENNReal.ofReal |f r|)
  have he s t : μ (Ioc s t) = ENNReal.ofReal (∫ r in Ioc s t, |f r| ∂ν.totalVariation) := by
    rw [withDensity_apply _ measurableSet_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal hf.abs.integrableOn (ae_of_all _ (fun r => abs_nonneg _))).symm
  rw [← he a b]
  apply interval_variation_le_increment_measure _ μ _ a b
  intro s t hst
  rw [signed_cumulative_increment ν f hf s t hst,he]
  apply ENNReal.ofReal_le_ofReal
  have hh := signed_integral_absolute_bound ν ((Ioc s t).indicator f) (hf.indicator measurableSet_Ioc)
  have heabs : (fun r => |(Ioc s t).indicator f r|) = (Ioc s t).indicator (fun r => |f r|) := by
    funext r
    by_cases hr : r ∈ Ioc s t <;> simp [hr]
  rw [heabs,integral_indicator measurableSet_Ioc] at hh
  exact hh

theorem signed_cumulative_boundedVariation (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν.totalVariation) (a b : ℝ) :
    BoundedVariationOn (signedCumulative ν f) (Icc a b) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (signed_cumulative_variation_bound ν f hf a b)

/-- The positive and negative variation combinations are each controlled
by twice the total-variation integral, as in exercise rep252(3). -/
theorem signed_integral_variation_combinations (ν : SignedMeasure ℝ) (f : ℝ → ℝ)
    (hf : Integrable f ν.totalVariation) :
    (∫ r, |f r| ∂ν.totalVariation)+signedIntegralRaw ν (fun r => |f r|) ≤
      2*(∫ r, |f r| ∂ν.totalVariation) ∧
    (∫ r, |f r| ∂ν.totalVariation)-signedIntegralRaw ν (fun r => |f r|) ≤
      2*(∫ r, |f r| ∂ν.totalVariation) := by
  have h := signed_integral_absolute_bound ν (fun r => |f r|) hf.abs
  simp only [abs_abs] at h
  obtain ⟨hn,hp⟩ := abs_le.mp h
  constructor <;> linarith

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_cumulative_variation_bound
#print axioms Asakura.Chapter2Complete.signed_integral_variation_combinations
