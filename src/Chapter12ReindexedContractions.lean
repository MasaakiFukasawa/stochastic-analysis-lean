import Chapter12IteratedContraction

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Finite tensor contractions allow arbitrary reorderings of the free
indices before the next contraction. All common indices are contracted
together, including the multiple edges produced by earlier mergers. -/
inductive ReindexedContraction : ℕ → Type
  | leaf {n : ℕ} (A : Fin n → ℝ) : ReindexedContraction n
  | reindex {m n : ℕ} (e : Fin m ≃ Fin n) (A : ReindexedContraction n) : ReindexedContraction m
  | join {i j k : ℕ} (A : ReindexedContraction (i*j)) (B : ReindexedContraction (j*k)) :
      ReindexedContraction (i*k)

noncomputable def ReindexedContraction.eval : {n : ℕ} → ReindexedContraction n → Fin n → ℝ
  | _,.leaf A => A
  | _,.reindex e A => fun x => A.eval (e x)
  | _,@ReindexedContraction.join i j k A B => fun x =>
      ∑ y : Fin j,A.eval (finProdFinEquiv ((finProdFinEquiv.symm x).1,y))*
        B.eval (finProdFinEquiv (y,(finProdFinEquiv.symm x).2))

noncomputable def ReindexedContraction.leafNormProduct : {n : ℕ} → ReindexedContraction n → ℝ
  | _,.leaf A => Real.sqrt (∑ x,A x^2)
  | _,.reindex _ A => A.leafNormProduct
  | _,.join A B => A.leafNormProduct*B.leafNormProduct

theorem reindexed_contraction_bound {n : ℕ} (C : ReindexedContraction n) :
    Real.sqrt (∑ x,C.eval x^2)≤C.leafNormProduct := by
  induction C with
  | leaf A => exact le_rfl
  | @reindex m n e A ih =>
    simpa only [ReindexedContraction.eval,ReindexedContraction.leafNormProduct,
      Equiv.sum_comp e (fun x => A.eval x^2)] using ih
  | @join i j k A B hA hB =>
    have hc := tensor_contraction_norm_bound
      (fun x y => A.eval (finProdFinEquiv (x,y)))
      (fun y z => B.eval (finProdFinEquiv (y,z)))
    rw [finite_product_square_sum,finite_product_square_sum] at hc
    have he : (∑ x : Fin i,∑ z : Fin k,
        (∑ y : Fin j,A.eval (finProdFinEquiv (x,y))*B.eval (finProdFinEquiv (y,z)))^2)=
        ∑ w,(ReindexedContraction.join A B).eval w^2 := by
      rw [← finite_product_square_sum i k]
      simp only [ReindexedContraction.eval,Equiv.symm_apply_apply]
    rw [he] at hc
    exact hc.trans (mul_le_mul hA hB (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hA))

theorem reindexed_scalar_contraction_bound (C : ReindexedContraction 1) :
    |C.eval 0|≤C.leafNormProduct := by
  have hh := reindexed_contraction_bound C
  simpa only [Fin.sum_univ_one,Real.sqrt_sq_eq_abs] using hh

end Asakura.Chapter12
