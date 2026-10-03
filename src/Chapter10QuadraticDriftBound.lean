import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The trace estimate is the expectation of the pointwise quadratic-form
bound; it does not require diagonalizing the error covariance. -/
theorem quadratic_drift_expectation_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Measure Ω) (X : Ω → E) (hX : MemLp X 2 P) (A : E →L[ℝ] E) :
    Integrable (fun w => 2*⟪X w,A (X w)⟫) P ∧
    (∫ w,2*⟪X w,A (X w)⟫ ∂P)≤2*‖A‖*(∫ w,‖X w‖^2 ∂P) := by
  have hb (w : Ω) : ‖2*⟪X w,A (X w)⟫‖≤(2*‖A‖)*‖X w‖^2 := by
    rw [norm_mul,Real.norm_ofNat]
    calc
      _ ≤ 2*(‖X w‖*‖A (X w)‖) := mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
      _ ≤ 2*(‖X w‖*(‖A‖*‖X w‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hi : Integrable (fun w => (2*‖A‖)*‖X w‖^2) P :=
    ((memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).mp hX).const_mul _
  have hg : Integrable (fun w => 2*⟪X w,A (X w)⟫) P := hi.mono'
    ((hX.aestronglyMeasurable.inner (A.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)).const_mul 2)
    (Filter.Eventually.of_forall hb)
  refine ⟨hg,?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hg hi (Filter.Eventually.of_forall fun w =>
    (le_abs_self _).trans (hb w))

end Asakura.Chapter10
