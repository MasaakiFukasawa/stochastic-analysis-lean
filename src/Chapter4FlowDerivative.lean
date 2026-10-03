import Chapter4LinearODEFactor
import Chapter5TimeReversePDE
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
open Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

lemma fin2_partial_time_derivative (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x y : ℝ) (k : Fin 2) :
    HasDerivAt (fun r => fderiv ℝ φ ![r,y] (Pi.single k 1))
      (fderiv ℝ (fderiv ℝ φ) ![x,y] (Pi.single 0 1) (Pi.single k 1)) x := by
  have hd := ((hφ.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable (by norm_num)) ![x,y]
  have hh := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single k (1:ℝ)) (![x,y] : Fin 2 → ℝ))).comp_hasDerivAt x
    (fin2_time_slice_derivative x y)
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,
    map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply,Function.comp_def] using hh

lemma fin2_partial_space_derivative (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x y : ℝ) (k : Fin 2) :
    HasDerivAt (fun r => fderiv ℝ φ ![x,r] (Pi.single k 1))
      (fderiv ℝ (fderiv ℝ φ) ![x,y] (Pi.single 1 1) (Pi.single k 1)) y := by
  have hd := ((hφ.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤2)).differentiable (by norm_num)) ![x,y]
  have hh := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single k (1:ℝ)) (![x,y] : Fin 2 → ℝ))).comp_hasDerivAt y
    (fin2_space_slice_derivative x y)
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply,
    map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply,Function.comp_def] using hh

/-- Differentiating the flow equation in its initial value is justified by
C2 regularity; Schwarz's theorem gives the variational ODE and its positive
exponential solution. -/
theorem flow_initial_derivative_positive
    (φ : (Fin 2 → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hflow : ∀ x y,fderiv ℝ φ ![x,y] (Pi.single 0 1)=f (φ ![x,y]))
    (hinit : ∀ y,φ ![0,y]=y) (x y : ℝ) :
    fderiv ℝ φ ![x,y] (Pi.single 1 1)=Real.exp (∫ r in 0..x,deriv f (φ ![r,y])) ∧
      0<fderiv ℝ φ ![x,y] (Pi.single 1 1) := by
  let q := fun r => fderiv ℝ φ ![r,y] (Pi.single 1 1)
  let a := fun r => deriv f (φ ![r,y])
  have ha : Continuous a := (hf.continuous_deriv le_rfl).comp (hφ.continuous.comp (by fun_prop))
  have hq r : HasDerivAt q (a r*q r) r := by
    have hspace := fin2_partial_space_derivative φ hφ r y 0
    have hfun : (fun s => fderiv ℝ φ ![r,s] (Pi.single 0 1))=(fun s => f (φ ![r,s])) := funext (hflow r)
    rw [hfun] at hspace
    have hright := (((hf.differentiable (by norm_num)) (φ ![r,y])).hasDerivAt).comp y
      (((hφ.differentiable (by norm_num)) ![r,y]).hasFDerivAt.comp_hasDerivAt y (fin2_space_slice_derivative r y))
    have he := hspace.unique hright
    have hsym := (hφ.contDiffAt (x := (![r,y] : Fin 2 → ℝ))).isSymmSndFDerivAt (by norm_num)
      (Pi.single 0 1) (Pi.single 1 1)
    have ht := fin2_partial_time_derivative φ hφ r y 1
    rw [hsym,he] at ht
    exact ht
  have hq0 : q 0=1 := by
    rw [show q 0=deriv (fun s => φ ![0,s]) y from fin2_space_derivative φ 0 y ((hφ.differentiable (by norm_num)) _)]
    rw [funext hinit]
    exact deriv_id y
  have he := linear_ode_exponential a q ha hq hq0 x
  refine ⟨he,?_⟩
  change 0<q x
  rw [he]
  exact Real.exp_pos _

end Asakura.Chapter4
