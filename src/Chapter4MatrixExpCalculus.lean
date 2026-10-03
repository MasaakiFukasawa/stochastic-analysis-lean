import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Matrix
open scoped Topology Matrix.Norms.Operator
namespace Asakura.Chapter4
set_option maxHeartbeats 2500000

noncomputable def matrixEntryCLM {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma matrix_exp_entry_derivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun r : ℝ => NormedSpace.exp (r • A) i j)
      ((A * NormedSpace.exp (t • A)) i j) t := by
  have hh := (matrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  exact hh

lemma matrix_exp_entry_smooth {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ContDiff ℝ 2 (fun r : ℝ => NormedSpace.exp (r • A) i j) := by
  have he : ContDiff ℝ 2 (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (matrixEntryCLM i j).contDiff.comp (he.comp (contDiff_id.smul contDiff_const))

end Asakura.Chapter4

namespace Asakura.Chapter4
lemma matrix_exp_inverse_product {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    NormedSpace.exp (t • A)*NormedSpace.exp ((-t) • A)=1 := by
  have hh := Matrix.exp_add_of_commute (t • A) (-(t • A)) (Commute.refl (t • A)).neg_right
  simp only [add_neg_cancel, NormedSpace.exp_zero] at hh
  simpa only [neg_smul] using hh.symm
end Asakura.Chapter4
