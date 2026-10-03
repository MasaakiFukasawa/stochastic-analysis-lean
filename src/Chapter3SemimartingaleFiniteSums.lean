import Chapter3OpenProcessRegularity
import Chapter3IncreasingAdaptedVariation
import Chapter2ElementaryFiniteSum
import Chapter2SemimartingaleDecomposition

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
  (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)

include hT in
theorem zero_local_process : LocalMProcessWitness P F (fun _ _ => 0) := by
  obtain ⟨c,_,_,_,hm,ht,hco⟩ := positive_real_time_exhaustion hT
  refine ⟨fun n _ => realTimeClamp (c n),?_,fun _ => hm.monotone,fun n _ => ht n,fun _ => hco,?_⟩
  · intro n t
    by_cases h : realTimeClamp (T := T) (c n) ≤ t <;> simp [h]
  · intro n
    exact (boundedMProcess P F).zero_mem

include hT hF in
theorem adapted_variation_finset_sum {ι : Type*} (s : Finset ι)
    (A : ι → ClosedTime T → Ω → ℝ) (hA : ∀ i ∈ s, AdaptedLocalVariationWitness F (A i)) :
    AdaptedLocalVariationWitness F (fun t ω => ∑ i ∈ s, A i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using continuous_increasing_adapted_variation hT F hF (fun _ _ => (0:ℝ))
      (fun _ _ => measurable_const) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hA i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))) hF

include hF in
/-- An AE Ito decomposition yields an exact decomposition by defining its
martingale part as the residual. Its local-martingale membership is proved. -/
theorem semimartingale_of_ae_decomposition
    (Y A M : ClosedTime T → Ω → ℝ)
    (ha : ∀ t, t < ⊤ → Measurable[F t] (Y t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y s ω) t)
    (hA : AdaptedLocalVariationWitness F A)
    (hAc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t)
    (hM : LocalMProcessWitness P F M)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → Y t ω = A t ω+M t ω) :
    SemimartingaleDecomposition P F Y A (fun t ω => Y t ω-A t ω) ∧
      ∀ᵐ ω ∂P, ∀ t, t < ⊤ → M t ω = Y t ω-A t ω := by
  have hm : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → M t ω = Y t ω-A t ω := by
    filter_upwards [he] with ω hω
    intro t ht
    linarith [hω t ht]
  refine ⟨⟨hA,LocalMProcessWitness.congr_ae_open P F hF hM
    (fun t ht => (ha t ht).sub (hA.adapted t ht))
    (fun ω t ht => (hc ω t ht).sub (hAc ω t ht)) hm,hc,?_⟩,hm⟩
  intro t ht ω
  ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.zero_local_process
#print axioms Asakura.Chapter3Complete.adapted_variation_finset_sum
#print axioms Asakura.Chapter3Complete.semimartingale_of_ae_decomposition
