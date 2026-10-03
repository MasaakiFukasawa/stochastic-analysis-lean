import Chapter12TensorContraction
import Mathlib.Logic.Equiv.Fin.Basic

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- A contraction tree joins different tensors and contracts all shared
indices at a join. The free indices are flattened finite products. -/
inductive ContractionTree : ℕ → Type
  | leaf {n : ℕ} (A : Fin n → ℝ) : ContractionTree n
  | join {i j k : ℕ} (A : ContractionTree (i*j)) (B : ContractionTree (j*k)) :
      ContractionTree (i*k)

noncomputable def ContractionTree.eval : {n : ℕ} → ContractionTree n → Fin n → ℝ
  | _, .leaf A => A
  | _, @ContractionTree.join i j k A B => fun x =>
      ∑ y : Fin j, A.eval (finProdFinEquiv ((finProdFinEquiv.symm x).1,y))*
        B.eval (finProdFinEquiv (y,(finProdFinEquiv.symm x).2))

noncomputable def ContractionTree.leafNormProduct : {n : ℕ} → ContractionTree n → ℝ
  | _, .leaf A => Real.sqrt (∑ x, A x^2)
  | _, .join A B => A.leafNormProduct*B.leafNormProduct

/-- Reindexing an array does not change its squared Hilbert norm. -/
theorem finite_product_square_sum (i j : ℕ) (A : Fin (i*j) → ℝ) :
    (∑ x : Fin i, ∑ y : Fin j, A (finProdFinEquiv (x,y))^2) = ∑ z,A z^2 := by
  calc
    _ = ∑ x : Fin i × Fin j, A (finProdFinEquiv x)^2 :=
      (Fintype.sum_prod_type (fun x : Fin i × Fin j => A (finProdFinEquiv x)^2)).symm
    _ = _ := Equiv.sum_comp finProdFinEquiv (fun z => A z^2)

theorem contraction_tree_bound {n : ℕ} (C : ContractionTree n) :
    Real.sqrt (∑ x, C.eval x^2) ≤ C.leafNormProduct := by
  induction C with
  | leaf A => exact le_rfl
  | @join i j k A B hA hB =>
    have hc := tensor_contraction_norm_bound
      (fun x y => A.eval (finProdFinEquiv (x,y)))
      (fun y z => B.eval (finProdFinEquiv (y,z)))
    rw [finite_product_square_sum,finite_product_square_sum] at hc
    have he : (∑ x : Fin i, ∑ z : Fin k,
        (∑ y : Fin j,A.eval (finProdFinEquiv (x,y))*B.eval (finProdFinEquiv (y,z)))^2) =
        ∑ w, (ContractionTree.join A B).eval w^2 := by
      rw [← finite_product_square_sum i k]
      simp only [ContractionTree.eval,Equiv.symm_apply_apply]
    rw [he] at hc
    exact hc.trans (mul_le_mul hA hB (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hA))

/-- A fully contracted scalar is bounded by the product of the norms of
its original tensors. The bound has no dimension-dependent factor. -/
theorem scalar_contraction_tree_bound (C : ContractionTree 1) :
    |C.eval 0| ≤ C.leafNormProduct := by
  have h := contraction_tree_bound C
  simpa only [Fin.sum_univ_one,Real.sqrt_sq_eq_abs] using h

end Asakura.Chapter12
