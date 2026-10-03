import Chapter12SymbolicGaussianFactors
import Chapter12GaussianJetProducts

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- One new edge label is reserved for the coordinate differentiated by
Gaussian duality. Ordinary factors give one branch and divergences two. -/
def SymbolicGaussianFactor.derivativeBranches {e : ℕ} :
    SymbolicGaussianFactor e → List (SymbolicGaussianFactor (e+1))
  | .plain ds out => [.plain (Fin.last e::ds.map Fin.castSucc) out.castSucc]
  | .divergence ds => [.plain (ds.map Fin.castSucc) (Fin.last e),
      .divergence (Fin.last e::ds.map Fin.castSucc)]

@[simp] theorem SymbolicGaussianFactor.eval_fresh_embedding {e n : ℕ}
    (f : SymbolicGaussianFactor e) (u : Fin (n+1) → GaussianJet (n+1))
    (a : Fin e → Fin (n+1)) (i : Fin (n+1)) :
    (f.reindex Fin.castSucc).eval u (Fin.snoc a i)=f.eval u a := by
  rw [SymbolicGaussianFactor.eval_reindex]
  congr 1
  funext j
  exact Fin.snoc_castSucc (α := fun _ : Fin (e+1) => Fin (n+1)) i a j

theorem SymbolicGaussianFactor.derivative_branch_identity {e n : ℕ}
    (f : SymbolicGaussianFactor e) (u : Fin (n+1) → GaussianJet (n+1))
    (a : Fin e → Fin (n+1)) (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (((f.eval u a).partial i).f x)=
      (f.derivativeBranches.map (fun g => (g.eval u (Fin.snoc a i)).f x)).sum := by
  have hm (ds : List (Fin e)) : (ds.map Fin.castSucc).map (Fin.snoc a i)=ds.map a := by
    simp [List.map_map,Function.comp_def]
  cases f with
  | plain ds out =>
    simp only [SymbolicGaussianFactor.derivativeBranches,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,SymbolicGaussianFactor.eval,Fin.snoc_castSucc,
      Fin.snoc_last,hm,GaussianJet.iteratedPartial]
  | divergence ds =>
    simp only [SymbolicGaussianFactor.derivativeBranches,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,SymbolicGaussianFactor.eval,Fin.snoc_last,hm,
      GaussianJet.iteratedPartial]
    exact GaussianJet.divergence_partial (fun j => (u j).iteratedPartial (ds.map a)) i x

theorem SymbolicGaussianFactor.derivative_branch_count {e : ℕ} (f : SymbolicGaussianFactor e) :
    f.derivativeBranches.length≤2 := by cases f <;> simp [SymbolicGaussianFactor.derivativeBranches]

end Asakura.Chapter12
