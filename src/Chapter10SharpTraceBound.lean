import Chapter10CovarianceTraceIdentity
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter10
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Exactly the Euclidean operator norm and factor two in the manuscript's
trace inequality, for the actual error covariance. -/
theorem covariance_sharp_trace_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : MemLp X 2 P)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hL : ∀ x i,L x i=(A*ᵥfun j => x j) i) :
    let S : Matrix (Fin d) (Fin d) ℝ := fun i j => ∫ w,X w i*X w j ∂P
    (A*S+S*A.transpose).trace≤2*‖L‖*S.trace := by
  intro S
  have hx i : MemLp (fun w => X w i) 2 P := by
    apply hX.norm.of_le ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp_aestronglyMeasurable hX.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun w => by
      simpa only [norm_norm] using PiLp.norm_apply_le (X w) i
  have htr : S.trace=∫ w,‖X w‖^2 ∂P := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finset_sum _ (fun i _ => (hx i).integrable_sq)]
    simp only [S,Matrix.trace,Matrix.diag_apply,pow_two]
  have hAs : (A*S).trace=∫ w,⟪X w,L (X w)⟫ ∂P := by
    rw [covariance_trace_contraction P (fun w i => X w i) hx A]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    simp only [PiLp.inner_apply,Real.inner_apply,hL]
  have hSs : S.transpose=S := by
    ext i j
    change (∫ w,X w j*X w i ∂P)=∫ w,X w i*X w j ∂P
    simp only [mul_comm]
  have hother : (S*A.transpose).trace=(A*S).trace := by
    rw [←Matrix.trace_transpose (S*A.transpose),Matrix.transpose_mul,Matrix.transpose_transpose,hSs]
  rw [Matrix.trace_add,hother,hAs,←two_mul,←integral_const_mul, htr]
  exact (quadratic_drift_expectation_bound P X hX L).2

end Asakura.Chapter10
