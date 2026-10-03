import Chapter12GaussianJetCommutation
import Chapter12DivergenceProfiles

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Free tensor indices are edge labels. The last, vector-valued index
is explicit for an ordinary derivative and is summed by divergence otherwise. -/
inductive SymbolicGaussianFactor (e : ℕ)
  | plain (derivatives : List (Fin e)) (output : Fin e)
  | divergence (derivatives : List (Fin e))
  deriving DecidableEq

def SymbolicGaussianFactor.reindex {e q : ℕ} (r : Fin e → Fin q) :
    SymbolicGaussianFactor e → SymbolicGaussianFactor q
  | .plain ds i => .plain (ds.map r) (r i)
  | .divergence ds => .divergence (ds.map r)

def SymbolicGaussianFactor.profile {e : ℕ} : SymbolicGaussianFactor e → IBPFactor
  | .plain ds _ => .plain ds.length
  | .divergence ds => .divergence ds.length

noncomputable def SymbolicGaussianFactor.eval {e n : ℕ} (u : Fin (n+1) → GaussianJet (n+1))
    (a : Fin e → Fin (n+1)) : SymbolicGaussianFactor e → GaussianJet (n+1)
  | .plain ds i => (u (a i)).iteratedPartial (ds.map a)
  | .divergence ds => GaussianJet.divergence (fun j => (u j).iteratedPartial (ds.map a))

@[simp] theorem SymbolicGaussianFactor.eval_reindex {e q n : ℕ}
    (r : Fin e → Fin q) (u : Fin (n+1) → GaussianJet (n+1))
    (a : Fin q → Fin (n+1)) (f : SymbolicGaussianFactor e) :
    (f.reindex r).eval u a=f.eval u (a ∘ r) := by
  cases f <;> simp [SymbolicGaussianFactor.reindex,SymbolicGaussianFactor.eval,List.map_map]

/-- Adding the selected output index turns a divergence factor into the
ordinary vector field on which the Gaussian duality formula acts. -/
theorem symbolic_selected_divergence {e n : ℕ} (ds : List (Fin e))
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1)) :
    (SymbolicGaussianFactor.divergence ds).eval u a=
      GaussianJet.divergence (fun i => (u i).iteratedPartial (ds.map a)) := rfl

/-- Differentiating an ordinary factor adds one derivative index. -/
theorem symbolic_plain_derivative {e n : ℕ} (ds : List (Fin e)) (out : Fin e)
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (((SymbolicGaussianFactor.plain ds out).eval u a).partial i).f x=
      ((u (a out)).iteratedPartial (i::ds.map a)).f x := rfl

/-- Differentiating a divergence factor creates exactly the two branches
used in the finite IBP recursion, with the correction carrying no new derivative. -/
theorem symbolic_divergence_derivative {e n : ℕ} (ds : List (Fin e))
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (((SymbolicGaussianFactor.divergence ds).eval u a).partial i).f x=
      ((u i).iteratedPartial (ds.map a)).f x+
      (GaussianJet.divergence (fun j => (u j).iteratedPartial (i::ds.map a))).f x := by
  exact GaussianJet.divergence_partial (fun j => (u j).iteratedPartial (ds.map a)) i x

end Asakura.Chapter12
