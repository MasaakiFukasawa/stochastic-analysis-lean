import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded

open Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter5
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true

theorem compact_cylinder_map_bound {E G : Type*} [TopologicalSpace E]
    [NormedAddCommGroup G] (g : E → G) (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ B : ℝ, ∀ x, ‖g x‖ ≤ B := hs.exists_bound_of_continuous hg

/-- The derivative maps of a smooth compactly supported cylinder have
compact support. The preceding norm bound therefore applies to each. -/
theorem smooth_compact_cylinder_derivatives_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hd : ∀ x, HasFDerivAt f (D x) x)
    (hdd : ∀ x, HasFDerivAt D (DD x) x) (hs : HasCompactSupport f) :
    HasCompactSupport D ∧ HasCompactSupport DD := by
  have he : fderiv ℝ f = D := funext (fun x => (hd x).fderiv)
  have hee : fderiv ℝ D = DD := funext (fun x => (hdd x).fderiv)
  have hsD : HasCompactSupport D := by rw [← he]; exact hs.fderiv ℝ
  have hsDD : HasCompactSupport DD := by rw [← hee]; exact hsD.fderiv ℝ
  exact ⟨hsD, hsDD⟩

end Asakura.Chapter5
