import Chapter12GaussianJetLinearProjection

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem GaussianJet.add_partial {n : ℕ} (f g : GaussianJet n) (i : Fin n) :
    (f.add g).partial i=(f.partial i).add (g.partial i) := by
  apply GaussianJet.ext_f
  funext x
  change fderiv ℝ (fun y => f.f y+g.f y) x (Pi.single i 1)=_
  rw [fderiv_fun_add ((f.smooth.differentiable (by simp)).differentiableAt)
    ((g.smooth.differentiable (by simp)).differentiableAt)]
  rfl

noncomputable def divergenceCommutatorTerms {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) : List (Fin (n+1)) → List (GaussianJet (n+1))
  | [] => []
  | i::ds => (u i).iteratedPartial ds :: (divergenceCommutatorTerms u ds).map (fun f => f.partial i)

noncomputable def gaussianJetListSum {n : ℕ} : List (GaussianJet n) → GaussianJet n
  | [] => GaussianJet.zero n
  | f::fs => f.add (gaussianJetListSum fs)

theorem divergenceCommutatorTerms_length {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (ds : List (Fin (n+1))) :
    (divergenceCommutatorTerms u ds).length=ds.length := by
  induction ds with
  | nil => rfl
  | cons i ds ih => simp only [divergenceCommutatorTerms,List.length_cons,List.length_map,ih]

theorem gaussianJetListSum_partial {n : ℕ} (fs : List (GaussianJet n)) (i : Fin n) :
    (gaussianJetListSum fs).partial i=gaussianJetListSum (fs.map (fun f => f.partial i)) := by
  induction fs with
  | nil =>
    apply GaussianJet.ext_f
    funext x
    simp [gaussianJetListSum,GaussianJet.partial,GaussianJet.zero]
  | cons f fs ih => simp only [gaussianJetListSum,List.map_cons,GaussianJet.add_partial,ih]

/-- After k derivatives the commutator has exactly k terms. Every term
is built by differentiating a component of u, while the remaining term
is the divergence of the differentiated field. -/
theorem gaussian_iterated_divergence_commutation {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (ds : List (Fin (n+1))) :
    (GaussianJet.divergence u).iteratedPartial ds=
      (gaussianJetListSum (divergenceCommutatorTerms u ds)).add
        (GaussianJet.divergence (fun j => (u j).iteratedPartial ds)) := by
  induction ds with
  | nil =>
    apply GaussianJet.ext_f
    funext x
    simp [GaussianJet.iteratedPartial,divergenceCommutatorTerms,gaussianJetListSum,GaussianJet.add,GaussianJet.zero]
  | cons i ds ih =>
    simp only [GaussianJet.iteratedPartial,ih,GaussianJet.add_partial,gaussianJetListSum_partial]
    apply GaussianJet.ext_f
    funext x
    change (gaussianJetListSum ((divergenceCommutatorTerms u ds).map (fun f => f.partial i))).f x+
      ((GaussianJet.divergence (fun j => (u j).iteratedPartial ds)).partial i).f x=_
    rw [GaussianJet.divergence_partial]
    change _=((u i).iteratedPartial ds).f x+
      (gaussianJetListSum ((divergenceCommutatorTerms u ds).map (fun f => f.partial i))).f x+
      (GaussianJet.divergence (fun j => ((u j).iteratedPartial ds).partial i)).f x
    ring

end Asakura.Chapter12
