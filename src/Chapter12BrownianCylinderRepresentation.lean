import Chapter12VectorWienerExists
import Chapter12WienerCylinder
import Chapter12WienerNontrivial

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- With the Wiener map constructed from the actual Brownian Ito integral,
equality of two cylindrical random variables implies equality of their
Malliavin derivatives. No separate Gaussian-law assumption remains. -/
theorem brownian_cylindrical_representation_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1)) :
    ∃ W : PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))) →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ (m k : ℕ)
        (u : Fin m → PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))))
        (v : Fin k → PiLp 2 (fun _ : Fin (d+1) => Lp ℝ 2 (volume.restrict (Ioi (0:ℝ)))))
        (f : (Fin m → ℝ) → ℝ) (g : (Fin k → ℝ) → ℝ)
        (Df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ)
        (Dg : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ),
        (∀ x, HasFDerivAt f (Df x) x) → (∀ x, HasFDerivAt g (Dg x) x) →
        ((fun w => f (fun j => W (u j) w)) =ᵐ[P] fun w => g (fun j => W (v j) w)) →
        (fun w => ∑ j, Df (fun j => W (u j) w) (Pi.single j 1) • u j) =ᵐ[P]
          fun w => ∑ j, Dg (fun j => W (v j) w) (Pi.single j 1) • v j := by
  letI := half_line_L2_nontrivial
  obtain ⟨W,hW,_⟩ := vector_actual_wiener_isometry_exists P B
  refine ⟨W,fun m k u v f g Df Dg hf hg he => ?_⟩
  exact wiener_cylindrical_derivative_independent P W univ dense_univ
    (fun h _ => hW h) u v f g Df Dg hf hg he

end Asakura.Chapter12
