import Chapter12HigherChainPartitions

namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def partitionArrayEquiv {k : ℕ} (c : OrderedFinpartition k) (N : Type*) :
    (Fin k → N) ≃ (∀i : Fin c.length,Fin (c.partSize i) → N) :=
  (Equiv.piCongrLeft (fun _ : Fin k => N) c.equivSigma).symm.trans
    (Equiv.piCurry (fun (i : Fin c.length) (_ : Fin (c.partSize i)) => N))

@[simp] theorem partitionArrayEquiv_apply {k : ℕ} (c : OrderedFinpartition k) (N : Type*)
    (a : Fin k → N) (i : Fin c.length) (j : Fin (c.partSize i)) :
    partitionArrayEquiv c N a i j=a (c.emb i j) := rfl

theorem partition_array_sum {k : ℕ} (c : OrderedFinpartition k) (N : Type*) [Fintype N]
    (f : (∀i : Fin c.length,Fin (c.partSize i) → N) → ℝ) :
    (∑a : Fin k → N,f (fun i => a ∘ c.emb i))=∑a,f a := by
  classical
  exact (partitionArrayEquiv c N).sum_comp f
end Asakura.Chapter12
#print axioms Asakura.Chapter12.partition_array_sum
