import Chapter5CylinderRecursionC2

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The Hessian on the varying coordinates is exactly the restriction
of the full Hessian, including when other coordinates encode time or
past observations. -/
theorem affine_restriction_hessian
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (L : V →L[ℝ] E) (x : E) (y u v : V) :
    fderiv ℝ (fderiv ℝ (fun z => f (x+L z))) y u v =
      fderiv ℝ (fderiv ℝ f) (x+L y) (L u) (L v) := by
  have hd z := (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt (x := z)
  have hdd z := ((hf.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable
    (by norm_num)).differentiableAt.hasFDerivAt (x := z)
  have he : fderiv ℝ (fun z => f (x+L z)) = fun z => (fderiv ℝ f (x+L z)).comp L := by
    funext z
    exact ((hd _).comp z (L.hasFDerivAt.const_add x)).fderiv
  rw [he]
  have hh := ((hdd _).comp y (L.hasFDerivAt.const_add x)).clm_comp (hasFDerivAt_const L y)
  simp only [ContinuousLinearMap.comp_zero,zero_add,Function.comp_def] at hh
  rw [hh.fderiv]
  rfl

end Asakura.Chapter5
