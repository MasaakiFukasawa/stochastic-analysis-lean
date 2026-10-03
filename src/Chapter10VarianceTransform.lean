import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Asakura.Chapter10

/-- Differentiating the reciprocal information yields the static Riccati
solution used in the first example. -/
theorem inverse_information_derivative (J : ℝ → ℝ) (x c σ : ℝ)
    (hJ : HasDerivAt J (c^2/σ^2) x) (hne : J x≠0) :
    HasDerivAt (fun t => (J t)⁻¹) (-(c^2*((J x)⁻¹)^2)/σ^2) x := by
  convert hJ.inv hne using 1 <;> ring

/-- Undo the deterministic rescaling of the state covariance. This includes
the varying-value exercise by retaining the incoming variance gamma^2. -/
theorem scaled_variance_derivative (S L : ℝ → ℝ) (t l b σ γ : ℝ)
    (hL : L t≠0) (hσ : σ≠0)
    (hdL : HasDerivAt L (l*b*L t) t)
    (hdS : HasDerivAt S
      (2*l*b*S t+(L t)^2*γ^2-b^2*(S t)^2/((L t)^2*σ^2)) t) :
    HasDerivAt (fun t => S t/(L t)^2)
      (γ^2-b^2*(S t/(L t)^2)^2/σ^2) t := by
  convert hdS.div (hdL.pow 2) (pow_ne_zero 2 hL) using 1
  simp only [Pi.pow_apply]
  field_simp [hL, hσ]
  ring

end Asakura.Chapter10
