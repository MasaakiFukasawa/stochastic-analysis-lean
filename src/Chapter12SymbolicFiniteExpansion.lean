import Chapter12SymbolicTermTransition
import Chapter12IBPExpansionLeaves
import Mathlib.Algebra.BigOperators.Fin

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- Repeated actual Gaussian IBP terminates in expectations with no
remaining divergence. It preserves all terms, the number of original
factors, and the derivative budget, with a dimension-free branch bound. -/
theorem symbolic_finite_ibp_expansion {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (t : SymbolicIBPTerm) (B : ℕ)
    (hB : 2*(t.size-1)≤B) :
    ∃ C : IBPExpansion,C.value=t.moment u ∧ C.BoundedBranches B t.pending ∧
      C.LeavesSatisfy (fun v => ∃ s : SymbolicIBPTerm,
        s.pending=0 ∧ s.size=t.size ∧ s.budget≤t.budget ∧ v=s.moment u) := by
  classical
  have main : ∀ r : ℕ,∀ t : SymbolicIBPTerm,t.pending=r → 2*(t.size-1)≤B →
      ∃ C : IBPExpansion,C.value=t.moment u ∧ C.BoundedBranches B r ∧
        C.LeavesSatisfy (fun v => ∃ s : SymbolicIBPTerm,
          s.pending=0 ∧ s.size=t.size ∧ s.budget≤t.budget ∧ v=s.moment u) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro t htr hB
      by_cases hr : r=0
      · exact ⟨.leaf (t.moment u),rfl,trivial,t,htr.trans hr,rfl,le_rfl,rfl⟩
      · obtain ⟨cs,he,hlen,hchildren⟩ := t.expand u (by omega)
        have hc (j : Fin cs.length) := hchildren (cs.get j) (List.get_mem cs j)
        have hex (j : Fin cs.length) := ih (cs.get j).pending (by simpa [htr] using (hc j).2.1)
          (cs.get j) rfl (by simpa only [(hc j).1] using hB)
        let children := fun j : Fin cs.length => Classical.choose (hex j)
        have hchild (j : Fin cs.length) := Classical.choose_spec (hex j)
        refine ⟨.split cs.length children,?_,?_,?_⟩
        · change (∑ j,(children j).value)=t.moment u
          calc
            _=∑ j,(cs.get j).moment u := Finset.sum_congr rfl (fun j _ => (hchild j).1)
            _=(cs.map (SymbolicIBPTerm.moment u)).sum := by
              rw [← List.sum_ofFn]
              change (List.ofFn ((SymbolicIBPTerm.moment u) ∘ cs.get)).sum=_
              rw [← List.map_ofFn,List.ofFn_get]
            _=t.moment u := he.symm
        · refine ⟨Nat.pos_of_ne_zero hr,hlen.trans hB,fun j => ?_⟩
          exact (children j).boundedBranches_mono B (cs.get j).pending (r-1)
            (hchild j).2.1 (by have := (hc j).2.1;omega)
        · intro j
          apply (children j).leavesSatisfy_mono (hchild j).2.2
          intro v hv
          obtain ⟨s,hs0,hss,hsb,hsv⟩ := hv
          exact ⟨s,hs0,hss.trans (hc j).1,hsb.trans (hc j).2.2,hsv⟩
  exact main t.pending t rfl hB

end Asakura.Chapter12
