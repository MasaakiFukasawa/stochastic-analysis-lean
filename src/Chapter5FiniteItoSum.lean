import Chapter5IntervalIntegralFormula
import Chapter2ElementaryFiniteSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Finite additivity for the actual covariance-characterized integral. -/
theorem ito_covariance_range_sum
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (H : ℕ → Ω × ℝ → ℝ) (M : ℕ → ClosedTime T → Ω → ℝ)
    (hM : ∀ j,LocalMProcessWitness P F (M j))
    (hI : ∀ j,ItoCovarianceFormula P F X (H j) (M j)) (N : ℕ) :
    LocalMProcessWitness P F (fun t w => ∑ j∈Finset.range N,M j t w) ∧
      ItoCovarianceFormula P F X (fun z => ∑ j∈Finset.range N,H j z)
        (fun t w => ∑ j∈Finset.range N,M j t w) := by
  have hzero : LocalMProcessWitness P F (fun _ _ => 0) := by
    simpa only [zero_mul] using hX.smul P F 0
  refine ⟨local_process_finset_sum P F hF hle (Finset.range N) M (fun j _ => hM j) hzero,?_⟩
  induction N with
  | zero =>
    have hh := (hI 0).add_smul P F hF hle X (M 0) (M 0) (H 0) (H 0) (hI 0) (-1)
    simpa only [neg_one_mul,neg_add_cancel,Finset.range_zero,Finset.sum_empty] using hh
  | succ N ih =>
    simpa only [Finset.sum_range_succ,one_mul] using ih.add_smul P F hF hle X _ _ _ _ (hI N) 1

end Asakura.Chapter5
