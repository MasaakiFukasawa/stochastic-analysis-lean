import Chapter8NewtonMatrixDriftLipschitz
import EndToEndSDEPathCoordinates

open MeasureTheory
open scoped NNReal
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Both physical drifts satisfy the chapter's sum-of-squares Lipschitz
condition. The finite-mass constant may depend on m, as it should. -/
theorem newton_mass_lipschitz {d : ℕ}
    (e : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (Γ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℝ≥0) (hg : LipschitzWith K g) (m : ℝ) :
    ∃ L : ℝ,0≤L ∧ ∀ x y : Fin (d+d) → ℝ,
      (∑i,((Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ) (e (velocityProjection d z))) j) i x)-
        (Fin.addCases (fun j z => velocityProjection d z j)
        (fun j z => e.symm (-m⁻¹ • g (e (positionProjection d z))-(m⁻¹ • Γ) (e (velocityProjection d z))) j) i y))^2)≤L*∑i,(x i-y i)^2 := by
  let A := m⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
  have hh : LipschitzWith (‖A‖₊*K) (fun z => m⁻¹ • g z) := A.lipschitz.comp hg
  simpa only [neg_smul] using newton_matrix_drift_lipschitz e (fun z => m⁻¹ • g z) _ hh (m⁻¹ • Γ)

theorem overdamped_drift_lipschitz {d : ℕ}
    (e : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (K : ℝ≥0) (hg : LipschitzWith K g) :
    ∃ L : ℝ,0≤L ∧ ∀ x y : Fin d → ℝ,
      (∑i,(e.symm (-M (g (e x))) i-e.symm (-M (g (e y))) i)^2)≤L*∑i,(x i-y i)^2 := by
  have hh := e.symm.toContinuousLinearMap.lipschitz.comp
    ((M.lipschitz.comp (hg.comp e.toContinuousLinearMap.lipschitz)).neg)
  refine ⟨d*(‖e.symm.toContinuousLinearMap‖₊*(‖M‖₊*(K*‖e.toContinuousLinearMap‖₊)):ℝ)^2,by positivity,?_⟩
  exact lipschitz_square_coordinates _ _ hh

#print axioms newton_mass_lipschitz
#print axioms overdamped_drift_lipschitz
end Asakura.EndToEnd
