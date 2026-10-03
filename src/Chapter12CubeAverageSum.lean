import Chapter12FiniteAverages
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem sum_snoc_cube {e N : ℕ} (f : (Fin (e+1) → Fin (N+1)) → ℝ) :
    (∑ b,f b)=∑ a : Fin e → Fin (N+1),∑ i : Fin (N+1),f (Fin.snoc a i) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (e+1) => Fin (N+1))) f,
    Fintype.sum_prod_type,Finset.sum_comm]
  rfl

theorem cubeAverage_eq_sum (N e : ℕ) (f : (Fin e → Fin (N+1)) → ℝ) :
    cubeAverage N e f=(∑ a,f a)/(N+1:ℝ)^e := by
  induction e with
  | zero =>
    simp only [cubeAverage,pow_zero,div_one,Fintype.sum_unique]
    congr 1
  | succ e ih =>
    change cubeAverage N e (fun a => finiteAverage (fun i => f (Fin.snoc a i)))=_
    rw [ih]
    simp only [finiteAverage]
    rw [← Finset.sum_div,div_div,← sum_snoc_cube,pow_succ']

noncomputable def finiteMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a,f a)/Fintype.card A

theorem cubeAverage_eq_finiteMean (N e : ℕ) (f : (Fin e → Fin (N+1)) → ℝ) :
    cubeAverage N e f=finiteMean f := by
  rw [cubeAverage_eq_sum]
  simp [finiteMean,Fintype.card_fun]

theorem finiteMean_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : finiteMean (fun a => f (e a))=finiteMean f := by
  unfold finiteMean
  rw [Equiv.sum_comp,Fintype.card_congr e]

theorem finiteMean_prod_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → ℝ) : finiteMean (fun ab : A × B => f ab.1)=finiteMean f := by
  unfold finiteMean
  rw [Fintype.sum_prod_type,Fintype.card_prod]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_mul]
  rw [← Finset.mul_sum]
  have hB : (Fintype.card B:ℝ)≠0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  field_simp

end Asakura.Chapter12
