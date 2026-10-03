import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach

open Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem smooth_global_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hbij : Function.Bijective f)
    (hd : ∀ x,Function.Bijective (fderiv ℝ f x)) :
    ∃ g : F → E,ContDiff ℝ ∞ g ∧ Function.LeftInverse g f ∧ Function.RightInverse g f := by
  let g := Function.invFun f
  have hleft : Function.LeftInverse g f := Function.leftInverse_invFun hbij.1
  have hright : Function.RightInverse g f := Function.rightInverse_invFun hbij.2
  refine ⟨g,?_,hleft,hright⟩
  apply contDiff_iff_contDiffAt.mpr
  intro y
  let x := g y
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective (fderiv ℝ f x)
    (LinearMap.ker_eq_bot.mpr (hd x).1) (LinearMap.range_eq_top.mpr (hd x).2)
  have hder : HasFDerivAt f (L : E →L[ℝ] F) x := by
    simpa only [L,ContinuousLinearEquiv.coe_ofBijective] using
      (hf.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=x)
  have hs := hf.contDiffAt.to_localInverse hder (by simp)
  have he : g =ᶠ[𝓝 (f x)] hf.contDiffAt.localInverse hder (by simp) := by
    have hstrict := hf.contDiffAt.hasStrictFDerivAt' hder (by simp)
    filter_upwards [hstrict.eventually_right_inverse] with z hz
    exact hbij.1 ((hright z).trans hz.symm)
  have hh := hs.congr_of_eventuallyEq he
  simpa only [x,hright y] using hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.smooth_global_inverse
