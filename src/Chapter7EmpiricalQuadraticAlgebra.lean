import Chapter7QuadraticTransform

open Matrix Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1600000

lemma triple_sum_rotate {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    (f : ι → κ → η → ℝ) : (∑ i,∑ j,∑ k,f i j k)=∑ k,∑ i,∑ j,f i j k := by
  calc
    _ = ∑ i,∑ k,∑ j,f i j k := sum_congr rfl (fun _ _ => sum_comm)
    _ = _ := sum_comm

lemma entry_contraction_trace {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose=A) : (∑ i,∑ j,H i j*A i j)=Matrix.trace (H*A) := by
  have hs : ∀ i j,A j i=A i j := fun i j => congrFun (congrFun hA i) j
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,hs]

lemma empirical_quadratic_algebra {d n : ℕ} (H S : Matrix (Fin d) (Fin d) ℝ)
    (D : Fin n → Fin d → ℝ) (T : ℝ) (hT : T≠0) (hn : 0<n) :
    (∑ i,∑ j,H i j*((1/T)*(∑ k,(S.mulVec (D k)) i*(S.mulVec (D k)) j)-(S*S.transpose) i j))=
      (1/T)*∑ k,((∑ i,∑ j,(S.transpose*H*S) i j*D k i*D k j)-(T/n)*(∑ i,(S.transpose*H*S) i i)) := by
  have hsym : (S*S.transpose).transpose=S*S.transpose := by simp only [Matrix.transpose_mul,Matrix.transpose_transpose]
  have htrace : (∑ i,∑ j,H i j*(S*S.transpose) i j)=(∑ i,(S.transpose*H*S) i i) := by
    rw [entry_contraction_trace H _ hsym,covariance_trace_transform]
    rfl
  have he : (∑ i,∑ j,H i j*((1/T)*(∑ k,(S.mulVec (D k)) i*(S.mulVec (D k)) j)))=
      (1/T)*∑ k,∑ i,∑ j,(S.transpose*H*S) i j*D k i*D k j := by
    have hr (i j : Fin d) : H i j*((1/T)*(∑ k,(S.mulVec (D k)) i*(S.mulVec (D k)) j))=
        (1/T)*∑ k,H i j*(S.mulVec (D k)) i*(S.mulVec (D k)) j := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    simp only [hr,← mul_sum]
    congr 1
    rw [triple_sum_rotate]
    apply sum_congr rfl
    intro k _
    exact quadratic_transform H S (D k)
  simp only [mul_sub,sum_sub_distrib]
  rw [he,htrace,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp
  <;> ring

end Asakura.Chapter7
