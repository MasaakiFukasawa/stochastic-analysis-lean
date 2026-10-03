import Chapter8NewtonMobility
import Chapter8FrictionScaling

open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Dividing the physical force by mass yields exactly the coordinate
SDE used by the energy proof. -/
theorem newton_mass_drift_identification {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Fin d → ℝ) ≃L[ℝ] E) (U : (Fin d → ℝ) → ℝ)
    (g : E → E) (m γ : ℝ)
    (hg : ∀ q,g (e q)=m⁻¹ • e (fun i => fderiv ℝ U q (Pi.single i 1))) :
    Fin.addCases (motive := fun _ : Fin (d+d) => (Fin (d+d) → ℝ) → ℝ) (fun i z => velocityProjection d z i)
      (fun i z => e.symm (-g (e (positionProjection d z))-(γ/m) • e (velocityProjection d z)) i)=
    Fin.addCases (motive := fun _ : Fin (d+d) => (Fin (d+d) → ℝ) → ℝ) (fun i z => velocityProjection d z i)
      (fun i z => -(fderiv ℝ U (positionProjection d z) (Pi.single i 1)+γ*velocityProjection d z i)/m) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> funext z
  · simp only [Fin.addCases_left]
  · simp only [Fin.addCases_right,hg,map_sub,map_neg,map_smul,e.symm_apply_apply,
      Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring

/-- Hessian bounds and differentiability rescale by the same positive mass;
the friction condition becomes the dimensionless condition in the energy proof. -/
theorem newton_mass_hessian_scaling {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (g : E → E) (H : E → E →L[ℝ] E)
    (hd : ∀ x,HasFDerivAt g (H x) x) (hH : Continuous H)
    (κ L m γ : ℝ) (hm : 0<m) (hκ : 0<κ) (hL : κ≤L)
    (hb : ∀ x z,κ*‖z‖^2≤⟪z,H x z⟫ ∧ ⟪z,H x z⟫≤L*‖z‖^2)
    (hγ : Real.sqrt m*(Real.sqrt L-Real.sqrt κ)<γ) :
    (∀ x,HasFDerivAt (fun y => m⁻¹ • g y) (m⁻¹ • H x) x) ∧
      Continuous (fun x => m⁻¹ • H x) ∧
      (∀ x z,(κ/m)*‖z‖^2≤⟪z,(m⁻¹ • H x) z⟫ ∧ ⟪z,(m⁻¹ • H x) z⟫≤(L/m)*‖z‖^2) ∧
      Real.sqrt (L/m)-Real.sqrt (κ/m)<γ/m := by
  refine ⟨fun x => (hd x).const_smul m⁻¹,(by fun_prop),?_,
    newton_friction_rescaling m γ κ L hm hκ.le (hκ.le.trans hL) hγ⟩
  intro x z
  simp only [ContinuousLinearMap.smul_apply,inner_smul_right]
  constructor
  · convert mul_le_mul_of_nonneg_left (hb x z).1 (inv_nonneg.mpr hm.le) using 1 <;> ring
  · convert mul_le_mul_of_nonneg_left (hb x z).2 (inv_nonneg.mpr hm.le) using 1 <;> ring

end Asakura.Chapter8
