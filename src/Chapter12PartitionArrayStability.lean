import Chapter12MultilinearArrayStability
import Chapter12PartitionArrayEquiv

namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem partition_array_stability {k : ℕ} (c : OrderedFinpartition k)
    {N E F : Type*} [Fintype N]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E [×c.length]→L[ℝ] F)
    (U V : ∀i : Fin c.length,(Fin (c.partSize i) → N) → E)
    (C D : Fin c.length → ℝ) (hC : ∀i,0≤C i) (hD : ∀i,0≤D i)
    (hU : ∀i,Real.sqrt (∑a,‖U i a‖^2)≤C i)
    (hV : ∀i,Real.sqrt (∑a,‖V i a‖^2)≤C i)
    (hUV : ∀i,Real.sqrt (∑a,‖U i a-V i a‖^2)≤D i) :
    Real.sqrt (∑a : Fin k → N,
      ‖A (fun i => U i (a ∘ c.emb i))-B (fun i => V i (a ∘ c.emb i))‖^2)≤
      ‖A-B‖*∏i,C i+∑i,‖B‖*(D i*∏j∈Finset.univ.erase i,C j) := by
  rw [partition_array_sum c N (fun a => ‖A (fun i => U i (a i))-B (fun i => V i (a i))‖^2)]
  exact multilinear_array_stability A B U V C D hC hD hU hV hUV
end Asakura.Chapter12
#print axioms Asakura.Chapter12.partition_array_stability
