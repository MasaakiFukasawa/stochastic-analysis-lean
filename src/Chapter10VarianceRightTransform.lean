import Chapter10VarianceTransform

namespace Asakura.Chapter10

/-- Undo the deterministic rescaling of the state covariance. This includes
the varying-value exercise by retaining the incoming variance gamma^2. -/
theorem scaled_variance_right_derivative (S L : ℝ → ℝ) (t l b σ γ : ℝ)
    (hL : L t≠0) (hσ : σ≠0)
    (hdL : HasDerivWithinAt L (l*b*L t) (Set.Ici t) t)
    (hdS : HasDerivWithinAt S
      (2*l*b*S t+(L t)^2*γ^2-b^2*(S t)^2/((L t)^2*σ^2)) (Set.Ici t) t) :
    HasDerivWithinAt (fun t => S t/(L t)^2)
      (γ^2-b^2*(S t/(L t)^2)^2/σ^2) (Set.Ici t) t := by
  convert hdS.div (hdL.pow 2) (pow_ne_zero 2 hL) using 1
  simp only [Pi.pow_apply]
  field_simp [hL, hσ]
  ring

end Asakura.Chapter10
