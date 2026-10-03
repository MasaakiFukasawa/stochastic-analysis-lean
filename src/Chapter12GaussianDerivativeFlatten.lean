import Chapter12GaussianIndexedVectorMoment
import Chapter12GaussianCommutatorNorm

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

noncomputable def tupleAppendEquiv (α : Type*) (j k : ℕ) :
    (Fin j → α) × (Fin k → α) ≃ (Fin (j+k) → α) where
  toFun ab := Fin.append ab.1 ab.2
  invFun b := (fun i => b (Fin.castAdd k i),fun i => b (Fin.natAdd j i))
  left_inv ab := by ext i <;> simp [Fin.append]
  right_inv b := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> simp [Fin.append]

theorem GaussianJet.iteratedPartial_append {n : ℕ} (f : GaussianJet n)
    (a b : List (Fin n)) :
    f.iteratedPartial (a++b)=(f.iteratedPartial b).iteratedPartial a := by
  induction a with
  | nil => rfl
  | cons i a ih => simp only [List.cons_append,GaussianJet.iteratedPartial,ih]

theorem gaussian_derivative_norm_split {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (j : ℕ) (x : Fin (n+1) → ℝ) :
    gaussianDerivativeNorm u j x=Real.sqrt (∑ i,∑ b : Fin j → Fin (n+1),
      ((u i).iteratedPartial (List.ofFn b)).f x^2) := by
  unfold gaussianDerivativeNorm gaussianArrayNorm
  congr 1
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin (n+1))),Fintype.sum_prod_type]
  simp only [gaussianDerivativeArray,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]

theorem gaussian_higher_derivative_flatten {n : ℕ}
    (u : Fin (n+1) → GaussianJet (n+1)) (j k : ℕ) (x : Fin (n+1) → ℝ) :
    gaussianArrayNorm (fun ab : (Fin k → Fin (n+1)) × (Fin (j+1) → Fin (n+1)) =>
      gaussianDerivativeArray (fun i => (u i).iteratedPartial (List.ofFn ab.1)) j ab.2) x=
      gaussianDerivativeNorm u (j+k) x := by
  classical
  rw [gaussian_derivative_norm_split]
  unfold gaussianArrayNorm
  congr 1
  rw [Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (j+1) => Fin (n+1))),Fintype.sum_prod_type]
  simp only [gaussianDerivativeArray,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  have hh := Equiv.sum_comp (tupleAppendEquiv (Fin (n+1)) j k)
    (fun b => ((u i).iteratedPartial (List.ofFn b)).f x^2)
  simpa only [Fintype.sum_prod_type,tupleAppendEquiv,Equiv.coe_fn_mk,List.ofFn_fin_append,GaussianJet.iteratedPartial_append] using hh

end Asakura.Chapter12
