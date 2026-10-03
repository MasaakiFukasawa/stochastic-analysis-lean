import Chapter12SymbolicFactorSelection

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

structure SymbolicIBPTerm where
  edges : ℕ
  factors : List (SymbolicGaussianFactor edges)

def SymbolicIBPTerm.pending (t : SymbolicIBPTerm) : ℕ := ibpPending (symbolicProfiles t.factors)
def SymbolicIBPTerm.budget (t : SymbolicIBPTerm) : ℕ :=
  ibpOrders (symbolicProfiles t.factors)+t.pending
def SymbolicIBPTerm.size (t : SymbolicIBPTerm) : ℕ := t.factors.length
noncomputable def SymbolicIBPTerm.moment {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1))
    (t : SymbolicIBPTerm) : ℝ := symbolicTermMoment u t.factors

@[simp] theorem symbolic_profiles_card {e : ℕ} (fs : List (SymbolicGaussianFactor e)) :
    (symbolicProfiles fs).card=fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [symbolicProfiles,ih]

theorem symbolic_child_transition_bounds {e : ℕ} (ds : List (Fin e))
    (fs : List (SymbolicGaussianFactor e)) (gs : List (SymbolicGaussianFactor (e+1)))
    (hg : gs∈symbolicIBPChildren ds fs) :
    gs.length=fs.length+1 ∧
    ibpPending (symbolicProfiles gs)< ibpPending (symbolicProfiles (.divergence ds::fs)) ∧
    ibpOrders (symbolicProfiles gs)+ibpPending (symbolicProfiles gs)≤
      ibpOrders (symbolicProfiles (.divergence ds::fs))+ibpPending (symbolicProfiles (.divergence ds::fs)) := by
  obtain ⟨hs,hhs,rfl⟩ := List.mem_map.mp hg
  have hh := ibp_profile_step_bounds (symbolic_branch_profile_step ds.length fs hs hhs)
  have he : symbolicProfiles (SymbolicGaussianFactor.plain (ds.map Fin.castSucc) (Fin.last e)::hs)=
      IBPFactor.plain ds.length::ₘsymbolicProfiles hs := by simp [symbolicProfiles,SymbolicGaussianFactor.profile]
  have he' : symbolicProfiles (SymbolicGaussianFactor.divergence ds::fs)=
      IBPFactor.divergence ds.length::ₘsymbolicProfiles fs := rfl
  have hc := hh.1
  simp only [Multiset.card_cons,symbolic_profiles_card] at hc
  refine ⟨by simpa using hc,?_,?_⟩
  · simpa only [he,he'] using hh.2.1
  · simpa only [he,he'] using hh.2.2

/-- A nonterminal actual contracted expectation has a bounded finite
expansion into strictly smaller ranks, preserving size and derivative budget. -/
theorem SymbolicIBPTerm.expand {n : ℕ} (u : Fin (n+1) → GaussianJet (n+1))
    (t : SymbolicIBPTerm) (ht : 0<t.pending) :
    ∃ cs : List SymbolicIBPTerm,
      t.moment u=(cs.map (SymbolicIBPTerm.moment u)).sum ∧
      cs.length≤2*(t.size-1) ∧
      ∀ c∈cs,c.size=t.size ∧ c.pending<t.pending ∧ c.budget≤t.budget := by
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
    refine ⟨hh.1.trans hsize.symm,?_,?_⟩
    · change ibpPending (symbolicProfiles gs)< ibpPending (symbolicProfiles t.factors)
      rw [hp]
      exact hh.2.1
    · change ibpOrders (symbolicProfiles gs)+ibpPending (symbolicProfiles gs)≤
        ibpOrders (symbolicProfiles t.factors)+ibpPending (symbolicProfiles t.factors)
      rw [hp]
      exact hh.2.2

end Asakura.Chapter12
