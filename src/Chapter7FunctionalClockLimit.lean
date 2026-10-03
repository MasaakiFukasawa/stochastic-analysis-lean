import Chapter7PathClockProbability
import Chapter7JointClockDistribution

open MeasureTheory Set Filter TopologicalSpace ProbabilityTheory
open scoped NNReal Topology ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1500000

/-- The functional limit after the DDS representation: the clocks need only
converge pointwise in probability and the continuous driving paths have one
common law. Independence between each path and its clock is not needed. -/
theorem functional_clock_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → Ω → C(ℝ≥0,ℝ)) (B0 : Ω → C(ℝ≥0,ℝ))
    (A : ℕ → Ω → C(ℝ≥0,ℝ≥0))
    (hB : ∀ n,Measurable (B n)) (hB0 : Measurable B0)
    (hA : ∀ n,Measurable (A n)) (hLaw : ∀ n,IdentDistrib (B n) B0 P P)
    (hm : ∀ n w,Monotone (A n w))
    (hp : ∀ t : ℝ≥0,TendstoInMeasure P (fun n w => A n w t) atTop (fun _ => t)) :
    TendstoInDistribution (fun n w => (B n w).comp (A n w)) atTop B0 (fun _ => P) P := by
  letI : MetricSpace C(ℝ≥0,ℝ) := metrizableSpaceMetric _
  letI : MetricSpace C(ℝ≥0,ℝ≥0) := metrizableSpaceMetric _
  have hprob : TendstoInMeasure P A atTop (fun _ => ContinuousMap.id ℝ≥0) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro ε hε
    have h := monotone_clock_path_neighborhood_probability P A hm hp
      (Metric.ball (ContinuousMap.id ℝ≥0) ε) (Metric.ball_mem_nhds _ hε)
    simpa only [Metric.mem_ball,not_lt] using h
  have hj := joint_clock_distribution P B A B0 (ContinuousMap.id ℝ≥0) hB hA hB0 hLaw hprob
  have hc := hj.continuous_comp clock_composition_continuous
  simpa only [Function.comp_def,ContinuousMap.comp_id] using hc

end Asakura.Chapter7
