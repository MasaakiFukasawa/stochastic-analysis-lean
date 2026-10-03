import Chapter7EstimatorCovariancePositive
import Chapter7EmpiricalQuadraticAlgebra

open Matrix Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma symmetric_covariance_contraction {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℝ)
    (hH : ∀ i j,H j i=H i j) (hA : ∀ i j,A j i=A i j) :
    (∑ i,∑ j,∑ k,∑ l,H i j*(A i k*A j l+A i l*A j k)*H k l)=
      2*Matrix.trace (H*A*H*A) := by
  let V := ∑ i,∑ j,∑ k,∑ l,H i j*A i k*A j l*H k l
  have hfirst : V=Matrix.trace (H*A*H*A) := by
    symm
    rw [Matrix.mul_assoc (H*A) H A]
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,sum_mul,mul_sum]
    have hswap : (∑ j,∑ k,∑ l,∑ i,(H j i*A i k)*(H k l*A l j)) =
        ∑ j,∑ k,∑ i,∑ l,(H j i*A i k)*(H k l*A l j) := by
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      exact sum_comm
    rw [hswap]
    rw [triple_sum_rotate (fun j k i => ∑ l,(H j i*A i k)*(H k l*A l j))]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    rw [hH i j,hA j l]
    ring
  have hsecond : (∑ i,∑ j,∑ k,∑ l,H i j*A i l*A j k*H k l)=V := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    rw [hH k l]
  have hex (i j k l : Fin d) : H i j*(A i k*A j l+A i l*A j k)*H k l=
      H i j*A i k*A j l*H k l+H i j*A i l*A j k*H k l := by ring
  simp only [hex,sum_add_distrib]
  rw [hsecond,← hfirst]
  ring

lemma estimator_covariance_contraction {d : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.transpose=H) :
    dotProduct (fun p : Fin d × Fin d => H p.1 p.2)
      ((estimatorLimitCovariance S).mulVec (fun p => H p.1 p.2))=
      2*(∑ i,∑ j,(S.transpose*H*S) i j^2) := by
  have hs : (S*S.transpose).transpose=S*S.transpose := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  rw [← covariance_trace_square H S hH]
  simp only [dotProduct,Matrix.mulVec,Fintype.sum_prod_type,estimatorLimitCovariance,mul_sum]
  simpa only [mul_assoc] using symmetric_covariance_contraction H (S*S.transpose)
    (fun i j => congrFun (congrFun hH i) j) (fun i j => congrFun (congrFun hs i) j)

end Asakura.Chapter7
