import BrownianProcessUnit
import Mathlib.Probability.HasLawExists

open MeasureTheory ProbabilityTheory Set
namespace Asakura

/-- Existence of the Gaussian process with Brownian covariance on the unit interval,
before selecting continuous sample paths. -/
theorem unit_gaussian_process_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ X : ℝ → Ω → ℝ,
      (∀ t, Measurable (X t)) ∧ IsGaussianProcess X P ∧
      (∀ t, (∫ ω, X t ω ∂P) = 0) ∧
      (∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1, (∫ ω, X s ω * X t ω ∂P) = min s t) := by
  obtain ⟨Ω, mΩ, P, ξ, hξm, hξ, hI, hP⟩ := exists_iid ℕ (gaussianReal 0 1)
  letI := mΩ
  letI := hP
  refine ⟨Ω, mΩ, P, hP, fourierProcess ξ hξ, ?_, fourier_process_gaussian ξ hξ hI,
    fourier_process_mean ξ hξ hI, ?_⟩
  · intro t
    exact (Lp.stronglyMeasurable (brownianHilbert (normalLp ξ hξ) t)).measurable
  · intro s hs t ht
    exact fourier_process_covariance ξ hξ hI s t hs ht
end Asakura
