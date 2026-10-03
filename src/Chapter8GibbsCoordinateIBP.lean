import Chapter8GibbsIntegrationByParts

open MeasureTheory
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The Gibbs integration-by-parts formula in any fixed direction. All
three integrability conditions are derived from the density's second moment
and the displayed growth bounds. -/
theorem gibbs_coordinate_integration_by_parts {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    (U : E → ℝ) (g : E → E →L[ℝ] ℝ) (β : ℝ)
    (hU : ∀ x, HasFDerivAt U (g x) x)
    (hg : Continuous g)
    (hi : Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x)))
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (hD : Continuous D)
    (hf : ∀ x, HasFDerivAt f (D x) x) (v : E)
    (A B C : ℝ) (hb : ∀ x, ‖f x‖ ≤ A*(1+‖x‖^2))
    (hd : ∀ x, ‖D x v‖ ≤ B*(1+‖x‖^2))
    (hprod : ∀ x, ‖g x v*f x‖ ≤ C*(1+‖x‖^2)) :
    (∫ x : E, Real.exp (-β*U x)*D x v) =
      β*(∫ x : E, Real.exp (-β*U x)*g x v*f x) := by
  let ρ := fun x => Real.exp (-β*U x)
  let Dρ := fun x => (-β*ρ x) • g x
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
  have hp := integrable_gibbs_polynomial_bound volume ρ (fun x => g x v*f x) hρpos hi
    (hρ.mul ((hg.clm_apply continuous_const).mul hfc)).aestronglyMeasurable C hprod
  have hf'g : Integrable (fun x => Dρ x v*f x) := by
    convert hp.const_mul (-β) using 1
    funext x
    simp [Dρ,ContinuousLinearMap.smul_apply]
    ring
  have hh := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ)
    hf'g hfg' hfg (fun x _ => hdρ x) (fun x _ => hf x)
  have he : (∫ x, Dρ x v*f x) = (-β)*(∫ x, ρ x*g x v*f x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp [Dρ,ContinuousLinearMap.smul_apply]
    ring
  change (∫ x, ρ x*D x v) = -(∫ x, Dρ x v*f x) at hh
  rw [he,neg_mul,neg_neg] at hh
  exact hh

end Asakura.Chapter8
