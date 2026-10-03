import Chapter7CovarianceMatrixAlgebra

open Finset
open scoped BigOperators
namespace Asakura.Chapter7

lemma quadratic_product_algebra {d : ℕ} (K I : Fin d → Fin d → ℝ) (x : Fin d → ℝ) (t : ℝ)
    (hK : ∀ i j,K i j=K j i)
    (hp : ∀ i j,x i*x j=I i j+I j i+(if i=j then t else 0)) :
    (∑ i,∑ j,K i j*x i*x j)-t*(∑ i,K i i)=2*(∑ i,∑ j,K i j*I i j) := by
  classical
  have he : (∑ i,∑ j,K i j*I j i)=(∑ i,∑ j,K i j*I i j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hK j i]
  have hd : (∑ i,∑ j,K i j*(if i=j then t else 0))=t*(∑ i,K i i) := by
    simp only [mul_ite,mul_zero]
    simp [← sum_mul,← mul_sum,mul_comm]
  have hx : (∑ i,∑ j,K i j*x i*x j)=
      (∑ i,∑ j,K i j*I i j)+(∑ i,∑ j,K i j*I j i)+(∑ i,∑ j,K i j*(if i=j then t else 0)) := by
    simp only [mul_assoc,hp,mul_add,sum_add_distrib]
  rw [hx,he,hd]
  ring

end Asakura.Chapter7
