import Chapter6IntegratingFactor
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory Set
namespace Asakura.Chapter10
open Asakura.Chapter6

lemma integrating_factor_C1 (a : ℝ → ℝ) (ha : Continuous a) :
    ContDiff ℝ 1 (linearIntegratingFactor a) := by
  have hd := integrating_factor_derivative a ha
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt,?_⟩
  have he : deriv (linearIntegratingFactor a)=(fun t => a t*linearIntegratingFactor a t) :=
    funext (fun t => (hd t).deriv)
  rw [he]
  exact ha.mul (integrating_factor_continuous a ha)

lemma integrating_factor_nonzero (a : ℝ → ℝ) (t : ℝ) : linearIntegratingFactor a t≠0 :=
  (Real.exp_pos _).ne'

lemma integrating_factor_initial (a : ℝ → ℝ) : linearIntegratingFactor a 0=1 := by
  simp [linearIntegratingFactor]

end Asakura.Chapter10
