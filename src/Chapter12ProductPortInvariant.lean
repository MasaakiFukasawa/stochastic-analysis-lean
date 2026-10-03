import Chapter12ContractionPorts

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Product differentiation adds one fresh endpoint to precisely one
factor. Existing endpoints remain distinct within every factor. -/
theorem symbolic_product_port_invariant {e : ℕ}
    (fs : List (SymbolicGaussianFactor e))
    (hf : ∀ f∈fs,f.ports.Nodup)
    (gs : List (SymbolicGaussianFactor (e+1))) (hg : gs∈symbolicProductBranches fs) :
    contractionPorts gs=Fin.last e::ₘ((contractionPorts fs).map Fin.castSucc) ∧
      ∀ g∈gs,g.ports.Nodup := by
  induction fs generalizing gs with
  | nil => simp [symbolicProductBranches] at hg
  | cons f fs ih =>
    have hf0 := hf f (List.mem_cons_self)
    have hfs : ∀ g∈fs,g.ports.Nodup := fun g hg => hf g (List.mem_cons_of_mem _ hg)
    simp only [symbolicProductBranches,List.mem_append,List.mem_map] at hg
    rcases hg with ⟨g,hg,rfl⟩ | ⟨hs,hhs,rfl⟩
    · constructor
      · simp [contractionPorts,derivative_branch_ports f g hg,← Multiset.singleton_add,
          add_comm,add_left_comm,add_assoc]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact derivative_branch_nodup f hf0 _ hg
        · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
          rw [factor_ports_reindex]
          exact (hfs a ha).map (Fin.castSucc_injective e)
    · obtain ⟨hports,hnodup⟩ := ih hfs hs hhs
      constructor
      · simp [contractionPorts,hports,← Multiset.singleton_add,add_comm,add_left_comm,add_assoc]
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [factor_ports_reindex]
          exact hf0.map (Fin.castSucc_injective e)
        · exact hnodup q hq

end Asakura.Chapter12
