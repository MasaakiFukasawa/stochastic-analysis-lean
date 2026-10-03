import Chapter9GaussianMixture
import Chapter9PosteriorBounds

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Normalize the strictly positive likelihood to a probability measure.
This is the posterior appearing in the score and covariance formulas. -/
theorem normalized_density_probability {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (k : E → ℝ) (hm : Measurable k) (hi : Integrable k μ)
    (hp : ∀ x,0≤k x) (hZ : 0<∫ x,k x ∂μ) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (k x/(∫ y,k y ∂μ)))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (hi.div_const _) (ae_of_all _ (fun x => div_nonneg (hp x) hZ.le)),
    integral_div,div_self hZ.ne',ENNReal.ofReal_one]

/-- The expectation under this constructed probability measure is the
ratio of weighted integrals, not an assumed conditional expectation. -/
theorem normalized_density_integral {E V : Type*} [MeasurableSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure E) (k : E → ℝ) (hm : Measurable k) (hp : ∀ x,0≤k x)
    (Z : ℝ) (hZ : 0<Z) (f : E → V) :
    (∫ x,f x ∂μ.withDensity (fun x => ENNReal.ofReal (k x/Z)))=
      Z⁻¹ • (∫ x,k x • f x ∂μ) := by
  rw [integral_withDensity_eq_integral_toReal_smul (hm.div_const Z).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (div_nonneg (hp _) hZ.le)]
  rw [←integral_smul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [smul_smul]
  congr 1
  exact div_eq_inv_mul _ _

/-- Likelihood weighting cannot create mass outside the support of the
prior. In particular the original bound on |X0| remains a posterior bound. -/
theorem normalized_density_preserves_ae {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (k : E → ℝ) (Z : ℝ) (A : Set E) (hA : ∀ᵐ x ∂μ,x∈A) :
    ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (k x/Z)),x∈A :=
  (withDensity_absolutelyContinuous μ _).ae_le hA
end Asakura.Chapter9
