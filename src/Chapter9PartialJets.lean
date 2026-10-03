import Chapter9GaussianCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

/-- Partial derivatives of a jointly smooth function remain jointly smooth.
The derivative is taken only in the second argument; the first argument
will later be integrated against an arbitrary initial law. -/
theorem joint_partial_jets_smooth {X E V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Set (X × E)) (f : X × E → V)
    (hf : ∀ z∈U,ContDiffAt ℝ ∞ f z) (n : ℕ) :
    ∀ z∈U,ContDiffAt ℝ ∞
      (fun q : X × E => iteratedFDeriv ℝ n (fun y => f (q.1,y)) q.2) z := by
  induction n with
  | zero =>
    intro z hz
    exact (hf z hz).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E V).symm : _ →L[ℝ] E [×0]→L[ℝ] V)
  | succ n ih =>
    intro z hz
    have hh : ContDiffAt ℝ ∞ (fun q : (X × E) × E =>
        iteratedFDeriv ℝ n (fun y => f (q.1.1,y)) q.2) (z,z.2) :=
      (ih z hz).comp (g := fun q : X × E => iteratedFDeriv ℝ n (fun y => f (q.1,y)) q.2) (z,z.2)
        (show ContDiffAt ℝ ∞ (fun q : (X × E) × E => (q.1.1,q.2)) (z,z.2) by fun_prop)
    have hd := hh.fderiv (n := ∞) (m := ∞)
      (f := fun q : X × E => fun y : E => iteratedFDeriv ℝ n (fun w => f (q.1,w)) y) (g := fun q : X × E => q.2)
      (show ContDiffAt ℝ ∞ (fun q : X × E => q.2) z by fun_prop) (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) V).symm :
        _ →L[ℝ] E [×(n+1)]→L[ℝ] V)

theorem ou_weight_smooth {d : ℕ} (j : Option (Fin d × Bool)) :
    ContDiff ℝ ∞ (ouWeight j) := by
  cases j with
  | none => unfold ouWeight; fun_prop
  | some j => rcases j with ⟨i,b⟩; cases b <;> unfold ouWeight <;> fun_prop

theorem ou_kernel_joint_smooth {d : ℕ} (x : Fin d → ℝ) (z : ℝ × (Fin d → ℝ))
    (hz : 0<z.1) :
    ContDiffAt ℝ ∞ (fun q : (Fin d → ℝ) × (ℝ × (Fin d → ℝ)) =>
      Real.exp (ouExponent q.1 q.2)) (x,z) := by
  apply ContDiffAt.exp
  simp_rw [ou_exponent_coefficients]
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul
  · exact (ou_weight_smooth j).contDiffAt.comp (x,z) contDiffAt_fst
  · exact ((ou_coefficient_smooth j).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hz)).comp (x,z) contDiffAt_snd
end Asakura.Chapter9
