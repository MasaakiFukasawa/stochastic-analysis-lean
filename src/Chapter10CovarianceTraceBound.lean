import Chapter10ErrorCovariancePositive
import Mathlib.Analysis.Matrix.Normed

open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Every entry of an actual covariance matrix is controlled by its trace.
Thus a trace bound rules out finite-time escape in matrix space. -/
theorem covariance_norm_le_trace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (e : Fin d → Ω → ℝ) (he : ∀ i,MemLp (e i) 2 P) :
    let V : Matrix (Fin d) (Fin d) ℝ := fun i j => ∫ w,e i w*e j w ∂P
    ‖V‖≤V.trace := by
  dsimp only
  let q := fun w => ∑ k,(e k w)^2
  have hq : Integrable q P := integrable_finset_sum _ (fun k _ => (he k).integrable_sq)
  have hqn w : 0≤q w := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have heq : (∫ w,q w ∂P)=Matrix.trace (show Matrix (Fin d) (Fin d) ℝ from fun i j => ∫ w,e i w*e j w ∂P) := by
    rw [integral_finset_sum _ (fun k _ => (he k).integrable_sq)]
    simp only [Matrix.trace,Matrix.diag_apply,pow_two]
  have hnonneg : 0≤Matrix.trace (show Matrix (Fin d) (Fin d) ℝ from fun i j => ∫ w,e i w*e j w ∂P) := by
    rw [←heq]
    exact integral_nonneg hqn
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro j
  have hb w : ‖e i w*e j w‖≤q w := by
    have hi : (e i w)^2≤q w := Finset.single_le_sum (f := fun k => (e k w)^2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hj : (e j w)^2≤q w := Finset.single_le_sum (f := fun k => (e k w)^2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> nlinarith [sq_nonneg (e i w-e j w),sq_nonneg (e i w+e j w)]
  calc
    ‖∫ w,e i w*e j w ∂P‖ ≤ ∫ w,‖e i w*e j w‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ w,q w ∂P := integral_mono ((he i).integrable_mul (he j)).norm hq hb
    _ = _ := heq

end Asakura.Chapter10
