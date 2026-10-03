import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Asakura.Chapter11
set_option maxHeartbeats 1200000

noncomputable def barrierReflection (ν : ℝ) (f : ℝ → ℝ) (y : ℝ) := Real.exp (-ν*y)*f (-y)

theorem barrier_reflection_deriv (ν y : ℝ) (f g : ℝ → ℝ)
    (hf : HasDerivAt f (g (-y)) (-y)) :
    HasDerivAt (barrierReflection ν f)
      (Real.exp (-ν*y)*(-ν*f (-y)-g (-y))) y := by
  have he := (((hasDerivAt_id y).const_mul (-ν)).exp).mul
    (hf.comp y (hasDerivAt_id y).neg)
  convert he using 1
  · rfl
  · simp only [mul_one,Pi.neg_apply,id_eq,Function.comp_def]
    ring

theorem barrier_reflection_second_deriv (ν y : ℝ) (f g h : ℝ → ℝ)
    (hf : ∀ y,HasDerivAt f (g y) y) (hg : HasDerivAt g (h (-y)) (-y)) :
    HasDerivAt (fun z => deriv (barrierReflection ν f) z)
      (Real.exp (-ν*y)*(ν^2*f (-y)+2*ν*g (-y)+h (-y))) y := by
  have he : (fun z => deriv (barrierReflection ν f) z)=
      (fun z => Real.exp (-ν*z)*(-ν*f (-z)-g (-z))) :=
    funext (fun z => (barrier_reflection_deriv ν z f g (hf (-z))).deriv)
  rw [he]
  have hfn := (hf (-y)).comp y (hasDerivAt_id y).neg
  have hgn := hg.comp y (hasDerivAt_id y).neg
  have hh := (((hasDerivAt_id y).const_mul (-ν)).exp).mul
    ((hfn.const_mul (-ν)).sub hgn)
  convert hh using 1
  · rfl
  · simp only [Pi.neg_apply,Pi.sub_apply,id_eq,mul_one,Function.comp_def]
    ring

/-- The spatial log-price generator commutes with the weighted reflection
precisely for nu = 2r/sigma^2 - 1. The zero-order term is retained. -/
theorem barrier_reflection_generator (r σ ν y f ft fy fyy : ℝ)
    (hν : σ^2*ν=2*r-σ^2) :
    Real.exp (-ν*y)*ft+(r-σ^2/2)*(Real.exp (-ν*y)*(-ν*f-fy))+
      σ^2/2*(Real.exp (-ν*y)*(ν^2*f+2*ν*fy+fyy))-r*(Real.exp (-ν*y)*f)=
      Real.exp (-ν*y)*(ft+(r-σ^2/2)*fy+σ^2/2*fyy-r*f) := by
  linear_combination (Real.exp (-ν*y)*(ν*f/2+fy))*hν

theorem barrier_reflection_parameter (r σ : ℝ) (hσ : σ≠0) :
    σ^2*(2*r/σ^2-1)=2*r-σ^2 := by field_simp <;> ring

theorem barrier_reflection_boundary (ν : ℝ) (f : ℝ → ℝ) :
    f 0-barrierReflection ν f 0=0 := by simp [barrierReflection]

end Asakura.Chapter11
