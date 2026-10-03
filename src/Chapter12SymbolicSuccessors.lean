import Chapter12SymbolicTermTransition

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def SymbolicIBPTerm.Successor (t c : SymbolicIBPTerm) : Prop :=
  ∃ (ds : List (Fin t.edges)) (fs : List (SymbolicGaussianFactor t.edges))
    (gs : List (SymbolicGaussianFactor (t.edges+1))),
    t.factors.Perm (.divergence ds::fs) ∧ gs∈symbolicIBPChildren ds fs ∧ c=⟨t.edges+1,gs⟩

theorem SymbolicIBPTerm.expand_successors {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (t : SymbolicIBPTerm) (ht : 0<t.pending) :
    ∃ cs : List SymbolicIBPTerm,
      t.moment u=(cs.map (SymbolicIBPTerm.moment u)).sum ∧
      cs.length≤2*(t.size-1) ∧
      ∀ c∈cs,c.size=t.size ∧ c.pending<t.pending ∧ c.budget≤t.budget ∧ t.Successor c := by
  obtain ⟨ds,fs,hperm⟩ := symbolic_select_divergence t.factors ht
  let cs := (symbolicIBPChildren ds fs).map (fun gs => (⟨t.edges+1,gs⟩ : SymbolicIBPTerm))
  have hp := symbolic_profiles_perm hperm
  have hsize : t.size=fs.length+1 := hperm.length_eq
  refine ⟨cs,?_,?_,?_⟩
  · change symbolicTermMoment u t.factors=_
    rw [symbolic_term_moment_perm u hperm,symbolic_term_ibp_expansion]
    simp only [cs,List.map_map,Function.comp_def,SymbolicIBPTerm.moment]
  · simpa only [cs,List.length_map,symbolicIBPChildren,List.length_map,hsize,Nat.add_sub_cancel] using
      symbolic_product_branch_count fs
  · intro c hc
    obtain ⟨gs,hgs,rfl⟩ := List.mem_map.mp hc
    have hh := symbolic_child_transition_bounds ds fs gs hgs
    refine ⟨hh.1.trans hsize.symm,?_,?_,ds,fs,gs,hperm,hgs,rfl⟩
    · change ibpPending (symbolicProfiles gs) < ibpPending (symbolicProfiles t.factors)
      rw [hp]
      exact hh.2.1
    · change ibpOrders (symbolicProfiles gs)+ibpPending (symbolicProfiles gs)≤
        ibpOrders (symbolicProfiles t.factors)+ibpPending (symbolicProfiles t.factors)
      rw [hp]
      exact hh.2.2

end Asakura.Chapter12
