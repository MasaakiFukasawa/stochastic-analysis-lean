import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Chapter12CharacteristicDecay

open MeasureTheory
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Rapid polynomial decay supplies every weighted integrability
hypothesis needed to differentiate the inverse Fourier integral. -/
theorem rapid_decay_polynomial_integrable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (φ : E → ℂ) (hm : AEStronglyMeasurable φ μ)
    (hdecay : ∀ k : ℕ,∃ A : ℝ,0≤A ∧ ∀ x,‖φ x‖≤A/(1+‖x‖)^k) :
    ∀ j : ℕ,Integrable (fun x => ‖x‖^j*‖φ x‖) μ := by
  intro j
  let r := Module.finrank ℝ E+1
  obtain ⟨A,hA,hbound⟩ := hdecay (j+r)
  have hi : Integrable (fun x : E => (1+‖x‖)^(-(r:ℝ))) μ :=
    integrable_one_add_norm (by dsimp only [r];norm_cast;omega)
  have hkernel : Integrable (fun x : E => A/(1+‖x‖)^r) μ := by
    convert hi.const_mul A using 1
    funext x
    rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
    rfl
  apply hkernel.mono' ((continuous_norm.pow j).aestronglyMeasurable.mul hm.norm)
  apply ae_of_all
  intro x
  change ‖‖x‖^j*‖φ x‖‖≤A/(1+‖x‖)^r
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤‖x‖^j*‖φ x‖)]
  calc
    _ ≤ (1+‖x‖)^j*(A/(1+‖x‖)^(j+r)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by linarith) j)
        (hbound x) (norm_nonneg _) (by positivity)
    _ = A/(1+‖x‖)^r := by
      rw [pow_add]
      field_simp

end Asakura.Chapter12
