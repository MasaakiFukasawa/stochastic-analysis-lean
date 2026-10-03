import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped BigOperators
namespace Asakura.Chapter9
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The determinant as the continuous multilinear function of its rows. -/
def determinantRows (n : Type*) [Fintype n] [DecidableEq n] :
    ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, by change Continuous (Matrix.det : Matrix n n ℝ → ℝ); fun_prop⟩

/-- Actual derivative of a matrix determinant, before using the variational ODE. -/
theorem determinant_path_derivative {n : Type*} [Fintype n] [DecidableEq n]
    (J : ℝ → Matrix n n ℝ) (V : Matrix n n ℝ) (t : ℝ)
    (hJ : HasDerivAt J V t) :
    HasDerivAt (fun s => (J s).det) (∑ i, ((J t).updateRow i (V i)).det) t := by
  have h := ((determinantRows n).hasFDerivAt (J t)).comp_hasDerivAt t hJ
  simpa only [ContinuousMultilinearMap.linearDeriv_apply,determinantRows,
    Matrix.det,Matrix.updateRow] using! h

/-- Substituting J'=AJ in the actual determinant derivative gives Jacobi's formula,
without assuming that J is invertible. -/
theorem determinant_variational_derivative {n : Type*} [Fintype n] [DecidableEq n]
    (J : ℝ → Matrix n n ℝ) (A : Matrix n n ℝ) (t : ℝ)
    (hJ : HasDerivAt J (A * J t) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t := by
  have h := determinant_path_derivative J (A*J t) t hJ
  have he i : ((J t).updateRow i ((A*J t) i)).det=A i i*(J t).det := by
    have hr : (A*J t) i=∑ j,A i j • (J t) j := by
      ext k
      simp [Matrix.mul_apply,Finset.sum_apply]
    rw [hr]
    change Matrix.detRowAlternating (Function.update (J t) i (∑ j,A i j • J t j))=_
    rw [AlternatingMap.map_update_sum]
    change (∑ j,((J t).updateRow i (A i j • J t j)).det)=_
    simp only [Matrix.det_updateRow_smul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Matrix.det_updateRow_eq_zero hji,mul_zero]
    · simp
  simp_rw [he] at h
  simpa only [Matrix.trace,Matrix.diag,Finset.sum_mul] using! h
end Asakura.Chapter9
