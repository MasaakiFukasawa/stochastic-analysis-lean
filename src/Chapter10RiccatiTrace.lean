import Chapter10RiccatiAlgebra
import Chapter10MatrixCovarianceUniqueness

open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The observation feedback removes a nonnegative term from the trace. -/
theorem riccati_feedback_trace_nonnegative {d r : ℕ}
    (S : Matrix (Fin d) (Fin d) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin d) ℝ) (R : Matrix (Fin r) (Fin r) ℝ)
    (hS : S.transpose=S) (hR : R.PosSemidef) (hK : K*R=S*C.transpose) :
    0≤(K*C*S).trace := by
  have hRt : R.transpose=R := by simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have ht := congrArg Matrix.transpose hK
  rw [transpose_mul,transpose_mul,transpose_transpose,hS,hRt] at ht
  have hpos : (K*R*K.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.mul_mul_conjTranspose_same K
  have he : K*R*K.transpose=K*C*S := by rw [Matrix.mul_assoc,ht,←Matrix.mul_assoc]
  rw [←he]
  exact hpos.trace_nonneg

lemma trace_abs_le_dimension_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    |A.trace|≤(d:ℝ)*‖A‖ := by
  calc
    _ ≤ ∑ i,|A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d,‖A‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (A i) i).trans (norm_le_pi_norm A i))
    _ = _ := by simp

/-- A matrix-norm trace bound sufficient for continuation. The sharper
Euclidean operator-norm factor in the text is handled by the quadratic-form estimate. -/
theorem riccati_trace_bound {d r : ℕ}
    (A S Q : Matrix (Fin d) (Fin d) ℝ) (K : Matrix (Fin d) (Fin r) ℝ)
    (C : Matrix (Fin r) (Fin d) ℝ) (R : Matrix (Fin r) (Fin r) ℝ)
    (hS : S.transpose=S) (hR : R.PosSemidef) (hK : K*R=S*C.transpose)
    (hbound : ‖S‖≤S.trace) :
    (A*S+S*A.transpose+Q-K*C*S).trace≤2*(d:ℝ)^2*‖A‖*S.trace+Q.trace := by
  have hneg := riccati_feedback_trace_nonnegative S K C R hS hR hK
  have hl := (le_abs_self (A*S).trace).trans ((trace_abs_le_dimension_norm (A*S)).trans
    (mul_le_mul_of_nonneg_left (elementwise_matrix_product_bound A S) (Nat.cast_nonneg d)))
  have hr := (le_abs_self (S*A.transpose).trace).trans ((trace_abs_le_dimension_norm (S*A.transpose)).trans
    (mul_le_mul_of_nonneg_left (elementwise_matrix_product_bound S A.transpose) (Nat.cast_nonneg d)))
  have hAt : ‖A.transpose‖=‖A‖ := Matrix.norm_transpose A
  rw [hAt] at hr
  have hmul : 2*(d:ℝ)^2*‖A‖*‖S‖≤2*(d:ℝ)^2*‖A‖*S.trace := by gcongr
  rw [Matrix.trace_sub,Matrix.trace_add,Matrix.trace_add]
  nlinarith

end Asakura.Chapter10
