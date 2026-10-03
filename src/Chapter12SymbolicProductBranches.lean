import Chapter12SymbolicDerivativeBranches

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def symbolicProductBranches {e : ℕ} : List (SymbolicGaussianFactor e) →
    List (List (SymbolicGaussianFactor (e+1)))
  | [] => []
  | f::fs =>
      f.derivativeBranches.map (fun g => g::fs.map (SymbolicGaussianFactor.reindex Fin.castSucc)) ++
      (symbolicProductBranches fs).map (fun gs => f.reindex Fin.castSucc::gs)

noncomputable def symbolicProductValue {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (fs : List (SymbolicGaussianFactor e)) (x : Fin (n+1) → ℝ) : ℝ :=
  (fs.map (fun f => (f.eval u a).f x)).prod

@[simp] theorem symbolicProductValue_cons {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1))
    (f : SymbolicGaussianFactor e) (fs : List (SymbolicGaussianFactor e)) (x : Fin (n+1) → ℝ) :
    symbolicProductValue u a (f::fs) x=(f.eval u a).f x*symbolicProductValue u a fs x := rfl

@[simp] theorem symbolicProductValue_embedding {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1)) (i : Fin (n+1))
    (fs : List (SymbolicGaussianFactor e)) (x : Fin (n+1) → ℝ) :
    symbolicProductValue u (Fin.snoc a i) (fs.map (SymbolicGaussianFactor.reindex Fin.castSucc)) x=
      symbolicProductValue u a fs x := by
  simp [symbolicProductValue,List.map_map,Function.comp_def]

private theorem sum_map_mul_right {A : Type*} (l : List A) (f : A → ℝ) (c : ℝ) :
    (l.map (fun a => f a*c)).sum=(l.map f).sum*c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,add_mul]

private theorem sum_map_mul_left {A : Type*} (l : List A) (f : A → ℝ) (c : ℝ) :
    (l.map (fun a => c*f a)).sum=c*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih,mul_add]

/-- This is the full product rule with the divergence commutators
expanded. The list contains at most twice the number of other factors. -/
theorem symbolic_product_branch_identity {e n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (a : Fin e → Fin (n+1)) (i : Fin (n+1))
    (fs : List (SymbolicGaussianFactor e)) (x : Fin (n+1) → ℝ) :
    ((GaussianJet.listProd (fs.map (fun f => f.eval u a))).partial i).f x=
      ((symbolicProductBranches fs).map
        (fun gs => symbolicProductValue u (Fin.snoc a i) gs x)).sum := by
  induction fs with
  | nil => simp [symbolicProductBranches,GaussianJet.listProd]
  | cons f fs ih =>
    rw [List.map_cons,GaussianJet.listProd,GaussianJet.mul_partial,ih,
      f.derivative_branch_identity u a i x]
    simp only [symbolicProductBranches,List.map_append,List.sum_append,List.map_map,
      Function.comp_def,symbolicProductValue_cons,symbolicProductValue_embedding,
      SymbolicGaussianFactor.eval_fresh_embedding]
    rw [sum_map_mul_right,sum_map_mul_left]
    congr 1
    rw [GaussianJet.listProd_apply]
    simp [symbolicProductValue,List.map_map,Function.comp_def]

theorem symbolic_product_branch_count {e : ℕ} (fs : List (SymbolicGaussianFactor e)) :
    (symbolicProductBranches fs).length≤2*fs.length := by
  induction fs with
  | nil => simp [symbolicProductBranches]
  | cons f fs ih =>
    simp only [symbolicProductBranches,List.length_append,List.length_map,List.length_cons]
    have hh := f.derivative_branch_count
    omega

end Asakura.Chapter12
