import Chapter12SymbolicProductBranches

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def symbolicProfiles {e : ℕ} : List (SymbolicGaussianFactor e) → Multiset IBPFactor
  | [] => 0
  | f::fs => f.profile ::ₘ symbolicProfiles fs

@[simp] theorem symbolic_factor_profile_reindex {e q : ℕ}
    (r : Fin e → Fin q) (f : SymbolicGaussianFactor e) : (f.reindex r).profile=f.profile := by
  cases f <;> simp [SymbolicGaussianFactor.reindex,SymbolicGaussianFactor.profile]

@[simp] theorem symbolic_profiles_reindex {e q : ℕ}
    (r : Fin e → Fin q) (fs : List (SymbolicGaussianFactor e)) :
    symbolicProfiles (fs.map (SymbolicGaussianFactor.reindex r))=symbolicProfiles fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [symbolicProfiles,ih]

theorem ibp_profile_step_cons (f : IBPFactor) {s t : Multiset IBPFactor}
    (h : IBPProfileStep s t) : IBPProfileStep (f::ₘs) (f::ₘt) := by
  cases h with
  | plain a b s =>
    simpa [← Multiset.singleton_add,add_comm,add_left_comm,add_assoc] using IBPProfileStep.plain a b (f::ₘs)
  | correction a b s =>
    simpa [← Multiset.singleton_add,add_comm,add_left_comm,add_assoc] using IBPProfileStep.correction a b (f::ₘs)
  | commute a b s =>
    simpa [← Multiset.singleton_add,add_comm,add_left_comm,add_assoc] using IBPProfileStep.commute a b (f::ₘs)

/-- Every branch of the actual symbolic product expansion obeys the
previously checked strict-rank and derivative-budget transition. -/
theorem symbolic_branch_profile_step {e : ℕ} (b : ℕ)
    (fs : List (SymbolicGaussianFactor e)) (gs : List (SymbolicGaussianFactor (e+1)))
    (hg : gs∈symbolicProductBranches fs) :
    IBPProfileStep (.divergence b::ₘsymbolicProfiles fs) (.plain b::ₘsymbolicProfiles gs) := by
  induction fs generalizing gs with
  | nil => simp [symbolicProductBranches] at hg
  | cons f fs ih =>
    simp only [symbolicProductBranches,List.mem_append,List.mem_map] at hg
    rcases hg with ⟨g,hg,rfl⟩ | ⟨gs,hgs,rfl⟩
    · cases f with
      | plain ds out =>
        simp only [SymbolicGaussianFactor.derivativeBranches,List.mem_singleton] at hg
        subst g
        simpa [symbolicProfiles,SymbolicGaussianFactor.profile] using
          IBPProfileStep.plain ds.length b (symbolicProfiles fs)
      | divergence ds =>
        simp only [SymbolicGaussianFactor.derivativeBranches,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hg
        rcases hg with rfl | rfl
        · simpa [symbolicProfiles,SymbolicGaussianFactor.profile] using
            IBPProfileStep.correction ds.length b (symbolicProfiles fs)
        · simpa [symbolicProfiles,SymbolicGaussianFactor.profile] using
            IBPProfileStep.commute ds.length b (symbolicProfiles fs)
    · have hh := ibp_profile_step_cons f.profile (ih gs hgs)
      simpa [symbolicProfiles,← Multiset.singleton_add,add_comm,add_left_comm,add_assoc] using hh

end Asakura.Chapter12
