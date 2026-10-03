import Chapter12BrownianForcingCovariance

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter13

theorem bond_ratio_ito_drift {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h k:E) : (‖k‖^2-‖h‖^2)/2+‖k-h‖^2/2=inner ℝ (k-h) k := by
  rw [norm_sub_sq_real,inner_sub_left,real_inner_self_eq_norm_sq,real_inner_comm h k]
  ring

theorem cumulative_covariance_drift {d n:ℕ}
    (a:Fin n → ℝ) (ha:∀i,a i≠0) (v:Fin n → EuclideanSpace ℝ (Fin d)) (j:Fin n) :
    ∑i∈Finset.Iic j,(a i)⁻¹*inner ℝ (a i • v i) (a j • v j)=
      a j*inner ℝ (v j) (∑i∈Finset.Iic j,v i) := by
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (v i) (v j)]
  field_simp [ha]

theorem cumulative_vectors {E:Type*} [AddCommGroup E] (H:ℕ → E) (j:ℕ) (h0:H 0=0) :
    ∑i∈Finset.range (j+1),(H (i+1)-H i)=H (j+1) := by
  induction j with
  | zero => simp [h0]
  | succ j ih => rw [Finset.sum_range_succ,ih];abel
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bond_ratio_ito_drift
#print axioms Asakura.Chapter13.cumulative_covariance_drift
