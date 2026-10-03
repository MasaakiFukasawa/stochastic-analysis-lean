import Chapter12ConcreteCylinderOperator
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem iterated_polynomial_growth_directional_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (v : E)
    (hg : ∀ k : ℕ,∃ C : ℝ,0≤C ∧ ∃ a : ℕ,∀ x,‖iteratedFDeriv ℝ k f x‖≤C*(1+‖x‖)^a)
    (k : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∃ a : ℕ,∀ x,
      ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖≤C*(1+‖x‖)^a := by
  obtain ⟨C,hC,a,hb⟩ := hg (k+1)
  refine ⟨‖v‖*C,mul_nonneg (norm_nonneg _) hC,a,fun x => ?_⟩
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hh := norm_iteratedFDeriv_clm_apply_const (c := v) (n := k) (x := x) hd.contDiffAt (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hh
  calc
    _≤‖v‖*‖iteratedFDeriv ℝ (k+1) f x‖ := hh
    _≤‖v‖*(C*(1+‖x‖)^a) := mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
    _=_ := by ring

/-- Every finite-coordinate partial derivative remains in the exact
smooth polynomial-growth cylinder class used to define D. -/
noncomputable def partialSmoothCylinder {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : SmoothCylinder H) (j : Fin c.dim) : SmoothCylinder H := by
  let g := fun x => fderiv ℝ c.f x (Pi.single j 1)
  have hg : ContDiff ℝ ∞ g :=
    (c.smooth.fderiv_right (by simp : ∞+1≤∞)).clm_apply contDiff_const
  have hb := iterated_polynomial_growth_directional_derivative c.f c.smooth (Pi.single j 1)
    c.all_derivatives_growth
  refine {
    dim := c.dim
    direction := c.direction
    f := g
    df := fderiv ℝ g
    smooth := hg
    derivative := fun x => (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
    growth := ?_
    derivative_measurable := ?_
    derivative_growth := ?_
    all_derivatives_growth := hb }
  · obtain ⟨C,hC,a,ha⟩ := hb 0
    refine ⟨C,hC,a,fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using ha x
  · intro i
    exact ((hg.fderiv_right (by simp : ∞+1≤∞)).clm_apply contDiff_const).continuous.measurable
  · intro i
    obtain ⟨C,hC,a,ha⟩ := iterated_polynomial_growth_directional_derivative g hg (Pi.single i 1) hb 0
    refine ⟨C,hC,a,fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using ha x

@[simp] theorem partialSmoothCylinder_function {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : SmoothCylinder H) (j : Fin c.dim) (x : Fin c.dim → ℝ) :
    (partialSmoothCylinder c j).f x=c.df x (Pi.single j 1) := by
  change fderiv ℝ c.f x (Pi.single j 1)=_
  rw [(c.derivative x).fderiv]

end Asakura.Chapter12
