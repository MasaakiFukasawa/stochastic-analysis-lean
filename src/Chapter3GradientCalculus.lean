import Chapter3MultivariateIto

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem coordinate_gradient_contDiff {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) (i : Fin d) :
    ContDiff ℝ 2 (fun x => fderiv ℝ f x (Pi.single i 1)) :=
  (hf.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).clm_apply contDiff_const

theorem coordinate_gradient_fderiv {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 3 f) (i : Fin d) (x v : Fin d → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x v =
      fderiv ℝ (fderiv ℝ f) x v (Pi.single i 1) := by
  have hd := (hf.fderiv_right (by norm_num : (2:WithTop ℕ∞)+1 ≤ 3)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simp

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.coordinate_gradient_contDiff
#print axioms Asakura.Chapter3Complete.coordinate_gradient_fderiv
