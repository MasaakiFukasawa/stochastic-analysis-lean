import Chapter12GaussianIteratedCommutation

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The k correction terms are the k permutations of D^(k-1)u:
each term uses one index for the value of u and every other index exactly
once for differentiation. -/
theorem divergenceCommutatorTerms_explicit {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (ds : List (Fin (n+1))) :
    divergenceCommutatorTerms u ds=
      ds.mapIdx (fun r i => (u i).iteratedPartial (ds.eraseIdx r)) := by
  induction ds with
  | nil => rfl
  | cons i ds ih =>
    simp only [divergenceCommutatorTerms,ih,List.mapIdx_cons,List.eraseIdx_cons_zero,
      List.eraseIdx_cons_succ,GaussianJet.iteratedPartial]
    congr 1
    simp only [List.mapIdx_eq_zipIdx_map,List.map_map,Function.comp_def]

end Asakura.Chapter12
