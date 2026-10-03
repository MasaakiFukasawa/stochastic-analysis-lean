import Chapter8OUStationary
import Chapter8GaussianProjection
import Chapter6LikelihoodQuadratic

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1000000

/-- The actual Gaussian second moment gives the information and the
asymptotic variance in the scalar OU estimation example. -/
theorem ou_information (θ σ : ℝ) (hθ : 0<θ) (hσ : 0<σ) :
    (∫ x : ℝ,x^2 ∂gaussianReal 0 (ouStationaryVariance θ σ hθ))=σ^2/(2*θ) ∧
    (σ^2)⁻¹*(∫ x : ℝ,x^2 ∂gaussianReal 0 (ouStationaryVariance θ σ hθ))=1/(2*θ) ∧
    ((σ^2)⁻¹*(∫ x : ℝ,x^2 ∂gaussianReal 0 (ouStationaryVariance θ σ hθ)))⁻¹=2*θ := by
  have hvar := variance_id_gaussianReal (μ := 0) (v := ouStationaryVariance θ σ hθ)
  rw [variance_eq_integral measurable_id.aemeasurable] at hvar
  simp only [integral_id_gaussianReal,id_eq,sub_zero] at hvar
  change (∫ x : ℝ,x^2 ∂gaussianReal 0 (ouStationaryVariance θ σ hθ))=σ^2/(2*θ) at hvar
  refine ⟨hvar,?_,?_⟩
  · rw [hvar]
    field_simp [hσ.ne',hθ.ne']
  · rw [hvar]
    field_simp [hσ.ne',hθ.ne']
    <;> ring

/-- The scalar quadratic likelihood gives the displayed estimator; the
known diffusion coefficient cancels exactly. -/
theorem ou_estimator_formula (σ A B : ℝ) (hσ : 0<σ) (hB : 0<B) :
    (((σ^2)⁻¹*B)⁻¹*(-(σ^2)⁻¹*A))= -A/B := by
  field_simp [hσ.ne',hB.ne']
  <;> ring

end Asakura.Chapter8
