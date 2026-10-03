import Chapter12TupleDeletion

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem mapIdx_ofFn_coordinates {α β : Type*} {k : ℕ} (b : Fin k → α)
    (f : ℕ → α → β) :
    (List.ofFn b).mapIdx f=List.ofFn (fun i => f i.val (b i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem gaussianJetListSum_apply {n : ℕ} (fs : List (GaussianJet n)) (x : Fin n → ℝ) :
    (gaussianJetListSum fs).f x=(fs.map (fun f => f.f x)).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simpa only [gaussianJetListSum,GaussianJet.add,List.map_cons,List.sum_cons] using congrArg (fun y => f.f x+y) ih

theorem gaussian_divergence_derivative_coordinates {n k : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (b : Fin (k+1) → Fin (n+1)) (x : Fin (n+1) → ℝ) :
    ((GaussianJet.divergence u).iteratedPartial (List.ofFn b)).f x=
      (∑ r : Fin (k+1),((u (b r)).iteratedPartial (List.ofFn (r.removeNth b))).f x)+
      (GaussianJet.divergence (fun i => (u i).iteratedPartial (List.ofFn b))).f x := by
  rw [gaussian_iterated_divergence_commutation]
  change (gaussianJetListSum (divergenceCommutatorTerms u (List.ofFn b))).f x+_=_
  congr 1
  rw [gaussianJetListSum_apply,divergenceCommutatorTerms_explicit,mapIdx_ofFn_coordinates]
  simp only [List.map_ofFn,List.sum_ofFn,ofFn_eraseIdx,Function.comp_def]

end Asakura.Chapter12
