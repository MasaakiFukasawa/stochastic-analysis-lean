import Chapter9JacobianTransport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise
namespace Asakura.Chapter9
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable def operatorMatrix {E n : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) : (E →L[ℝ] E) →L[ℝ] Matrix n n ℝ :=
  ((LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

 theorem operator_matrix_det {E n : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (A : E →L[ℝ] E) : (operatorMatrix b A).det=A.det :=
  LinearMap.det_toMatrix b A.toLinearMap

 theorem operator_matrix_mul {E n : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (A B : E →L[ℝ] E) :
    operatorMatrix b (A*B)=operatorMatrix b A*operatorMatrix b B :=
  LinearMap.toMatrix_mul b A.toLinearMap B.toLinearMap

/-- Jacobi's derivative is connected to the determinant of the actual
Fréchet-derivative operator used by the change-of-variables theorem. -/
theorem operator_determinant_derivative {E n : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    (b : Module.Basis n ℝ E) (J : ℝ → E →L[ℝ] E) (A : E →L[ℝ] E) (t : ℝ)
    (hJ : HasDerivAt J (A*J t) t) :
    HasDerivAt (fun s => (J s).det) ((operatorMatrix b A).trace*(J t).det) t := by
  have hd : HasDerivAt (fun s => operatorMatrix b (J s)) (operatorMatrix b (A*J t)) t := by
    simpa using (hasDerivAt_const t (operatorMatrix b)).clm_apply hJ
  rw [operator_matrix_mul] at hd
  have hh := determinant_variational_derivative (fun s => operatorMatrix b (J s))
    (operatorMatrix b A) t hd
  simpa only [operator_matrix_det] using hh
end Asakura.Chapter9
