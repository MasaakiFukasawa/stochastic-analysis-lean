import Chapter8GibbsDensity
import Chapter8GibbsIntegrability
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Quadratic growth times a Gibbs weight is integrable under the exact
second-moment hypothesis of the chapter. -/
theorem integrable_gibbs_polynomial_bound {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] (μ : Measure E) (ρ f : E → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hi : Integrable (fun x => (1+‖x‖^2)*ρ x) μ)
    (hf : AEStronglyMeasurable (fun x => ρ x*f x) μ)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C*(1+‖x‖^2)) :
    Integrable (fun x => ρ x*f x) μ := by
  apply (hi.const_mul C).mono' hf
  apply ae_of_all _
  intro x
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hρ x)]
  have hh := mul_le_mul_of_nonneg_left (hb x) (hρ x)
  convert hh using 1 <;> ring

/-- The Gibbs integration-by-parts formula in any fixed direction. All
three integrability conditions are derived from the density's second moment
and the displayed growth bounds. -/
theorem gibbs_directional_integration_by_parts {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (U : E → ℝ) (g : E → E) (β : ℝ)
    (hU : ∀ x, HasFDerivAt U (innerSL ℝ (g x)) x)
    (hg : Continuous g)
    (hi : Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x)))
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hD : Continuous D)
    (hf : ∀ x, HasFDerivAt f (D x) x) (v : E)
    (A B C : ℝ) (hb : ∀ x, ‖f x‖ ≤ A*(1+‖x‖^2))
    (hd : ∀ x, ‖D x v‖ ≤ B*(1+‖x‖^2))
    (hprod : ∀ x, ‖⟪g x,v⟫*f x‖ ≤ C*(1+‖x‖^2)) :
    (∫ x : E, Real.exp (-β*U x)*D x v) =
      β*(∫ x : E, Real.exp (-β*U x)*⟪g x,v⟫*f x) := by
  let ρ := fun x => Real.exp (-β*U x)
  let Dρ := fun x => (-β*ρ x) • innerSL ℝ (g x)
  have hUc : Continuous U := continuous_iff_continuousAt.mpr (fun x => (hU x).continuousAt)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hρ : Continuous ρ := by fun_prop
  have hdρ (x : E) : HasFDerivAt ρ (Dρ x) x := by
    have hh := ((hU x).const_mul (-β)).exp
    convert hh using 1
    ext z
    simp [Dρ,ρ,ContinuousLinearMap.smul_apply]
    ring
  have hρpos (x : E) : 0 ≤ ρ x := (Real.exp_pos _).le
  have hfg := integrable_gibbs_polynomial_bound volume ρ f hρpos hi
    (hρ.mul hfc).aestronglyMeasurable A hb
  have hfg' := integrable_gibbs_polynomial_bound volume ρ (fun x => D x v) hρpos hi
    (hρ.mul (hD.clm_apply continuous_const)).aestronglyMeasurable B hd
  have hp := integrable_gibbs_polynomial_bound volume ρ (fun x => ⟪g x,v⟫*f x) hρpos hi
    (hρ.mul ((hg.inner continuous_const).mul hfc)).aestronglyMeasurable C hprod
  have hf'g : Integrable (fun x => Dρ x v*f x) := by
    convert hp.const_mul (-β) using 1
    funext x
    simp [Dρ,ContinuousLinearMap.smul_apply,innerSL_apply_apply]
    ring
  have hh := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ)
    hf'g hfg' hfg (fun x _ => hdρ x) (fun x _ => hf x)
  have he : (∫ x, Dρ x v*f x) = (-β)*(∫ x, ρ x*⟪g x,v⟫*f x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [Dρ,ContinuousLinearMap.smul_apply,innerSL_apply_apply]
    ring
  change (∫ x, ρ x*D x v) = -(∫ x, Dρ x v*f x) at hh
  rw [he,neg_mul,neg_neg] at hh
  exact hh

end Asakura.Chapter8
