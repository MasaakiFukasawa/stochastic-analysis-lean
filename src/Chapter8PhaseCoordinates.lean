import Chapter8LinearPullbackDerivatives
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
namespace Asakura.Chapter8
noncomputable section
set_option maxHeartbeats 1400000

def positionProjection (d : ℕ) : (Fin (d+d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.castAdd d i))

def velocityProjection (d : ℕ) : (Fin (d+d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Fin.natAdd d i))

theorem phase_coordinate_disjoint {d : ℕ} (i j : Fin d) : Fin.castAdd d i ≠ Fin.natAdd d j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem phase_projection_basis {d : ℕ} (i : Fin d) :
    positionProjection d (Pi.single (Fin.castAdd d i) 1)=Pi.single i 1 ∧
    positionProjection d (Pi.single (Fin.natAdd d i) 1)=0 ∧
    velocityProjection d (Pi.single (Fin.castAdd d i) 1)=0 ∧
    velocityProjection d (Pi.single (Fin.natAdd d i) 1)=Pi.single i 1 := by
  constructor
  · ext j
    change (Pi.single (Fin.castAdd d i) (1:ℝ) : Fin (d+d) → ℝ) (Fin.castAdd d j)= (Pi.single i 1 : Fin d → ℝ) j
    simp [Pi.single_apply]
  constructor
  · ext j
    change (Pi.single (Fin.natAdd d i) (1:ℝ) : Fin (d+d) → ℝ) (Fin.castAdd d j)=0
    simp only [Pi.single_apply,if_neg (phase_coordinate_disjoint j i)]
  constructor
  · ext j
    change (Pi.single (Fin.castAdd d i) (1:ℝ) : Fin (d+d) → ℝ) (Fin.natAdd d j)=0
    simp only [Pi.single_apply,if_neg (phase_coordinate_disjoint i j).symm]
  · ext j
    change (Pi.single (Fin.natAdd d i) (1:ℝ) : Fin (d+d) → ℝ) (Fin.natAdd d j)= (Pi.single i 1 : Fin d → ℝ) j
    simp [Pi.single_apply]

theorem phase_sum_squares {d : ℕ} (z : Fin (d+d) → ℝ) :
    (∑ i,z i^2)=(∑ i,(positionProjection d z i)^2)+(∑ i,(velocityProjection d z i)^2) := by
  exact Fin.sum_univ_add (fun i => z i^2)

end
end Asakura.Chapter8
