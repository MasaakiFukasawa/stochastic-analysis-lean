import Chapter8PhaseCoordinates
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
namespace Asakura.Chapter8
noncomputable section

def phaseMeasurableEquiv (d : ℕ) :
    (Fin (d+d) → ℝ) ≃ᵐ ((Fin d → ℝ) × (Fin d → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (d+d) => ℝ)
    (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d))).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ))

theorem phase_measurable_equiv_apply (d : ℕ) (z : Fin (d+d) → ℝ) :
    phaseMeasurableEquiv d z=(positionProjection d z,velocityProjection d z) := rfl

theorem phase_volume_preserving (d : ℕ) :
    MeasurePreserving (phaseMeasurableEquiv d) volume volume := by
  exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin d ⊕ Fin d => ℝ)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (d+d) => ℝ)
      (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d+d))).symm _)

end
end Asakura.Chapter8
