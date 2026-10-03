import Chapter9OperatorJacobian
import Chapter9CenteredBilinear
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.Elementwise
namespace Asakura.Chapter9
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable def euclideanTrace (d : ℕ) :
    (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ :=
  (Matrix.traceLinearMap (Fin d) ℝ ℝ).toContinuousLinearMap.comp
    (operatorMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

 theorem euclidean_trace_apply {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanTrace d A=∑ i,A (EuclideanSpace.single i 1) i := by
  simp [euclideanTrace,operatorMatrix,Matrix.traceLinearMap,Matrix.trace,
    LinearMap.toMatrix_apply,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr]

 theorem euclidean_trace_identity (d : ℕ) :
    euclideanTrace d (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))=(d:ℝ) := by
  rw [euclidean_trace_apply]
  simp

 theorem euclidean_trace_dyad {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) :
    euclideanTrace d (dyad x y)=⟪x,y⟫ := by
  rw [euclidean_trace_apply]
  simp only [dyad_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    EuclideanSpace.inner_single_right,one_mul,PiLp.smul_apply,smul_eq_mul,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.single_apply,mul_comm]
end Asakura.Chapter9
