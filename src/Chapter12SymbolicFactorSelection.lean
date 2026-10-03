import Chapter12SymbolicTermMoments

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem symbolic_profiles_perm {e : ℕ} {fs gs : List (SymbolicGaussianFactor e)} (h : fs.Perm gs) :
    symbolicProfiles fs=symbolicProfiles gs := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [symbolicProfiles,ih]
  | swap a b l => exact Multiset.cons_swap _ _ _
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem symbolic_term_moment_perm {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) {fs gs : List (SymbolicGaussianFactor e)}
    (h : fs.Perm gs) : symbolicTermMoment u fs=symbolicTermMoment u gs := by
  unfold symbolicTermMoment
  congr 1
  funext a
  congr 1
  funext x
  exact (h.map (fun f => (f.eval u a).f x)).prod_eq

/-- A nonterminal contraction has a divergence factor that can be moved
to the front without changing its expectation or derivative budget. -/
theorem symbolic_select_divergence {e : ℕ} (fs : List (SymbolicGaussianFactor e))
    (h : 0< ibpPending (symbolicProfiles fs)) :
    ∃ ds rs,fs.Perm (SymbolicGaussianFactor.divergence ds::rs) := by
  induction fs with
  | nil => simp [symbolicProfiles,ibpPending] at h
  | cons f fs ih =>
    cases f with
    | divergence ds => exact ⟨ds,fs,List.Perm.refl _⟩
    | plain ds out =>
      have ht : 0< ibpPending (symbolicProfiles fs) := by
        simpa [symbolicProfiles,SymbolicGaussianFactor.profile,ibpPending,IBPFactor.pending] using h
      obtain ⟨ds',rs,he⟩ := ih ht
      exact ⟨ds',SymbolicGaussianFactor.plain ds out::rs,
        (List.Perm.cons _ he).trans (List.Perm.swap _ _ _)⟩

end Asakura.Chapter12
