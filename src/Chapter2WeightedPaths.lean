import Chapter2WeightedRepresentative
import Chapter2CumulativeIntegral
import Chapter2StieltjesRestriction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- Only continuity on the original interval is required for atomlessness. -/
theorem interval_stieltjes_no_atoms_on
    (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x, x ∈ Icc a b → ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (hc : ContinuousOn A (Icc a b)) :
    NullSingletonClass (intervalStieltjes a b hab A hA hr).measure := by
  constructor
  intro t
  rw [StieltjesFunction.measure_singleton]
  have hcont : Continuous (intervalStieltjes a b hab A hA hr) :=
    hc.comp_continuous (intervalClamp_continuous a b hab) (intervalClamp_mem a b hab)
  rw [hcont.continuousAt.continuousWithinAt.leftLim_eq,sub_self,ENNReal.ofReal_zero]

/-- Finite pathwise square energy gives continuity, an increasing
continuous decomposition, and initial value zero for the actual integral. -/
theorem weighted_cumulative_path_properties
    (a b : ℝ) (hab : a ≤ b) (A : ℝ → ℝ)
    (hA : MonotoneOn A (Icc a b))
    (hr : ∀ x, x ∈ Icc a b → ContinuousWithinAt A (Icc a b ∩ Ici x) x)
    (hc : ContinuousOn A (Icc a b)) (g : ℝ → ℝ) (hg : Measurable g)
    (henergy : (∫⁻ r, ENNReal.ofReal (g r ^ 2)
      ∂(intervalStieltjes a b hab A hA hr).measure) < ∞) :
    let μ := (intervalStieltjes a b hab A hA hr).measure
    MemLp g 2 μ ∧ Continuous (fun t => ∫ r in Iic t, g r ∂μ) ∧
      (∫ r in Iic a, g r ∂μ) = 0 ∧
      ∃ U V : ℝ → ℝ, Continuous U ∧ Continuous V ∧ Monotone U ∧ Monotone V ∧
        ∀ t, (∫ r in Iic t, g r ∂μ) = U t-V t := by
  let μ := (intervalStieltjes a b hab A hA hr).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite a b hab A hA hr
  letI : NullSingletonClass μ := interval_stieltjes_no_atoms_on a b hab A hA hr hc
  have hs : Integrable (fun r => g r ^ 2) μ := by
    refine ⟨(hg.pow_const 2).aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (.of_forall fun r => sq_nonneg (g r))).2 henergy
  have h2 := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hs
  have hi := h2.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  refine ⟨h2,continuous_cumulative_integral μ g hi,?_,cumulative_integral_continuous_jordan μ g hi⟩
  have hz : μ (Iic a) = 0 := by
    rw [StieltjesFunction.measure_Iic _
      (interval_stieltjes_left_limit a b hab (fun _ : Unit => A) (fun _ => hA) (fun _ => hr) () )]
    change ENNReal.ofReal (A (intervalClamp a b hab a)-A a) = 0
    rw [intervalClamp_eq a b hab (left_mem_Icc.2 hab),sub_self,ENNReal.ofReal_zero]
  rw [Measure.restrict_eq_zero.2 hz]
  simp

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.interval_stieltjes_no_atoms_on
#print axioms Asakura.Chapter2Complete.weighted_cumulative_path_properties
