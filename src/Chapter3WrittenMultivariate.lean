import Chapter3WrittenTaylor
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter3Written

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First derivative of the restriction to a spatial line segment. -/
theorem derivative_on_line {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) (t : ℝ) :
    deriv (fun s : ℝ => f (x+s • v)) t = (fderiv ℝ f (x+t • v)) v := by
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hl).deriv

/-- Second derivative on the segment equals the Hessian applied twice to v.
This supplies the calculus bridge, rather than assuming it as an input. -/
theorem second_derivative_on_line {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => f (x+s • v)) t =
      (fderiv ℝ (fderiv ℝ f) (x+t • v)) v v := by
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hc := (hd.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hl
  have ha := hc.clm_apply (hasDerivAt_const t v)
  have he : deriv (fun s : ℝ => f (x+s • v)) =
      (fun s => (fderiv ℝ f (x+s • v)) v) := funext (derivative_on_line hf x v)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [he]
  simpa using ha.deriv

/-- The corrected multidimensional Taylor estimate. Hessian oscillation is
controlled on the SEGMENT, which need not lie in the stochastic path image. -/
theorem multivariate_taylor_remainder {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ f) (x+t • v)-fderiv ℝ (fderiv ℝ f) x‖ ≤ δ) :
    |f (x+v)-f x-(fderiv ℝ f x) v-
      (fderiv ℝ (fderiv ℝ f) x) v v/2| ≤ δ*‖v‖^2/2 := by
  have hg : ContDiff ℝ 2 (fun s : ℝ => f (x+s • v)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hbound : ∀ t ∈ uIcc (0 : ℝ) 1,
      |iteratedDeriv 2 (fun s : ℝ => f (x+s • v)) t-
       iteratedDeriv 2 (fun s : ℝ => f (x+s • v)) 0| ≤ δ*‖v‖^2 := by
    intro t ht
    rw [second_derivative_on_line hf, second_derivative_on_line hf]
    simp only [zero_smul, add_zero]
    let D := fderiv ℝ (fderiv ℝ f) (x+t • v)-fderiv ℝ (fderiv ℝ f) x
    have hd : ‖D‖ ≤ δ := hosc t (by simpa using ht)
    have hnorm : ‖D v v‖ ≤ δ*‖v‖^2 := by
      calc
        _ ≤ ‖D v‖*‖v‖ := (D v).le_opNorm v
        _ ≤ (‖D‖*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg _)
        _ ≤ (δ*‖v‖)*‖v‖ := by gcongr
        _ = _ := by ring
    simpa only [D, sub_apply, Real.norm_eq_abs] using hnorm
  have h := taylor_second_order_oscillation hg
    (mul_nonneg hδ (sq_nonneg ‖v‖)) hbound
  simpa [derivative_on_line hf, second_derivative_on_line hf] using h

/-- In a fixed dimension, convergence of each quadratic variation sum gives
convergence of their sum; multiplying by a vanishing modulus kills the remainder. -/
theorem multivariate_remainder_limit {d : ℕ} (Q : Fin d → ℕ → ℝ) (q : Fin d → ℝ)
    (hQ : ∀ i, Tendsto (Q i) atTop (𝓝 (q i)))
    (w R : ℕ → ℝ) (hw : Tendsto w atTop (𝓝 0))
    (hR : ∀ n, |R n| ≤ w n * ∑ i, Q i n) :
    Tendsto R atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ i, Q i n) atTop (𝓝 (∑ i, q i)) :=
    tendsto_finsetSum _ (fun i _ => hQ i)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) hR
  simpa using hw.mul hsum

end Asakura.Chapter3Written
