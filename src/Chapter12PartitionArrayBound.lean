import Chapter12PartitionArrayEquiv
import Chapter12MultilinearArrayBound

namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem partition_array_norm_bound {k : ℕ} (c : OrderedFinpartition k)
    {N E F : Type*} [Fintype N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E [×c.length]→L[ℝ] F)
    (U : ∀i : Fin c.length,(Fin (c.partSize i) → N) → E) :
    Real.sqrt (∑a : Fin k → N,‖A (fun i => U i (a ∘ c.emb i))‖^2) ≤
      ‖A‖*∏i,Real.sqrt (∑a : Fin (c.partSize i) → N,‖U i a‖^2) := by
  rw [partition_array_sum c N (fun a => ‖A (fun i => U i (a i))‖^2)]
  exact multilinear_array_norm_bound A U
end Asakura.Chapter12
#print axioms Asakura.Chapter12.partition_array_norm_bound
