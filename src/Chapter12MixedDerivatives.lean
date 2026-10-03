import Chapter12Representation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace Asakura.Chapter12

/-- The equality of mixed derivatives required by the divergence commutator
is a consequence of genuine second Fréchet differentiability. -/
theorem cylinder_mixed_derivatives {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (Df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (D₂f : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (hf : ∀ z, HasFDerivAt f (Df z) z)
    (hdf : ∀ z, HasFDerivAt Df (D₂f z) z)
    (i j : Fin n) (z : Fin n → ℝ) :
    D₂f z (Pi.single i 1) (Pi.single j 1) =
      D₂f z (Pi.single j 1) (Pi.single i 1) :=
  second_derivative_symmetric hf (hdf z) _ _

end Asakura.Chapter12
