import Chapter7NaturalReturnSequence
import Chapter7BrownianOccupationSequence
import Chapter7PositiveOccupationIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 2200000

/-- Infinite occupation of [-1,1] from the original Brownian assumptions.
The return sequence and all conditional estimates are constructed by the
preceding proofs, rather than supplied as additional hypotheses. -/
theorem brownian_infinite_occupation_written
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w)) :
    ∀ᵐ w ∂P,volume {t : ℝ | 0 ≤ t ∧ |B t.toNNReal w| ≤ 1} = ∞ := by
  obtain ⟨τ,hτ,_,hret⟩ := natural_brownian_return_sequence P B hB hm hc
  exact brownian_occupation_of_returns P B hB hm hc τ hτ hret

/-- The positive continuous clock consequence used immediately afterwards
in the scale-function example. -/
theorem brownian_positive_clock_infinite
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (a : ℝ → ℝ) (ha : Continuous a) (hap : ∀ x,0 < a x) :
    ∀ᵐ w ∂P,(∫⁻ t in Ici (0:ℝ),ENNReal.ofReal (a (B t.toNNReal w))) = ∞ := by
  filter_upwards [brownian_infinite_occupation_written P B hB hm hc] with w hw
  apply positive_integral_of_infinite_occupation (volume.restrict (Ici (0:ℝ)))
    (fun t => B t.toNNReal w) ((hc w).comp continuous_real_toNNReal).measurable a ha hap
  have hmX : Measurable (fun t : ℝ => B t.toNNReal w) := ((hc w).comp continuous_real_toNNReal).measurable
  rw [Measure.restrict_apply (hmX (measurableSet_Icc : MeasurableSet (Icc (-1:ℝ) 1)))]
  convert hw using 1
  congr 1
  ext t
  simp only [mem_inter_iff,mem_preimage,mem_Icc,mem_Ici,mem_setOf_eq,abs_le]
  tauto

end Asakura.Chapter7
