import Chapter12RapidDecayIntegrable
import Mathlib.Analysis.Fourier.FourierTransformDeriv

open MeasureTheory Real
open scoped FourierTransform ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- All differentiations of the Fourier integral are justified by the
polynomial moments deduced from the characteristic-function decay. -/
theorem rapid_decay_fourier_smooth {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] V →L[ℝ] ℝ)
    (φ : E → ℂ) (hm : AEStronglyMeasurable φ μ)
    (hdecay : ∀ k : ℕ,∃ A : ℝ,0≤A ∧ ∀ x,‖φ x‖≤A/(1+‖x‖)^k) :
    ContDiff ℝ ∞ (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₁₂ φ) := by
  exact VectorFourier.contDiff_fourierIntegral L
    (N := ⊤) (fun j _ => rapid_decay_polynomial_integrable μ φ hm hdecay j)

end Asakura.Chapter12
