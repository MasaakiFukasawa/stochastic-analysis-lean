import Chapter8PhaseCoordinates
import Chapter8QuadraticDerivativeBounds

open scoped NNReal BigOperators
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
noncomputable section

def kineticBilinear (d : ℕ) (m : ℝ) :
    (Fin (d+d) → ℝ) →L[ℝ] (Fin (d+d) → ℝ) →L[ℝ] ℝ :=
  (m/2) • ∑ i : Fin d,
    ((ContinuousLinearMap.proj i).comp (velocityProjection d)).smulRight
      ((ContinuousLinearMap.proj i).comp (velocityProjection d))

theorem kinetic_bilinear_apply {d : ℕ} (m : ℝ) (x y : Fin (d+d) → ℝ) :
    kineticBilinear d m x y=(m/2)*∑ i,velocityProjection d x i*velocityProjection d y i := by
  simp [kineticBilinear,ContinuousLinearMap.sum_apply,Finset.sum_apply]

def newtonHamiltonian {d : ℕ} (U : (Fin d → ℝ) → ℝ) (m : ℝ) (z : Fin (d+d) → ℝ) : ℝ :=
  U (positionProjection d z)+kineticBilinear d m z z

theorem newton_hamiltonian_energy {d : ℕ} (U : (Fin d → ℝ) → ℝ) (m : ℝ) (z : Fin (d+d) → ℝ) :
    newtonHamiltonian U m z=U (positionProjection d z)+(m/2)*∑ i,(velocityProjection d z i)^2 := by
  simp only [newtonHamiltonian,kinetic_bilinear_apply,pow_two]

theorem newton_hamiltonian_regularity {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : ContDiff ℝ 3 U)
    (A₂ A₃ : ℝ≥0)
    (h₂ : ∀ x,‖fderiv ℝ (fderiv ℝ U) x‖≤(A₂:ℝ))
    (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ)) (m : ℝ) :
    ContDiff ℝ 3 (newtonHamiltonian U m) ∧ ∃ C₂ C₃ : ℝ≥0,
      (∀ x,‖fderiv ℝ (fderiv ℝ (newtonHamiltonian U m)) x‖≤(C₂:ℝ)) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (newtonHamiltonian U m))) x‖≤(C₃:ℝ)) := by
  obtain ⟨B₂,B₃,hB₂,hB₃⟩ := linear_pullback_derivative_bounds (positionProjection d) U hU A₂ A₃ h₂ h₃
  exact add_quadratic_derivative_bounds (fun x => U (positionProjection d x))
    (hU.comp (positionProjection d).contDiff) (kineticBilinear d m) B₂ B₃ hB₂ hB₃

theorem newton_hamiltonian_gradient {d : ℕ}
    (U : (Fin d → ℝ) → ℝ) (hU : Differentiable ℝ U) (m : ℝ) (z : Fin (d+d) → ℝ) (i : Fin d) :
    fderiv ℝ (newtonHamiltonian U m) z (Pi.single (Fin.castAdd d i) 1)=
      fderiv ℝ U (positionProjection d z) (Pi.single i 1) ∧
    fderiv ℝ (newtonHamiltonian U m) z (Pi.single (Fin.natAdd d i) 1)=
      m*velocityProjection d z i := by
  have hq : Differentiable ℝ (fun x => kineticBilinear d m x x) :=
    ((kineticBilinear d m).contDiff.clm_apply contDiff_id : ContDiff ℝ 1 _).differentiable (by norm_num)
  have hf : fderiv ℝ (newtonHamiltonian U m) z=
      (fderiv ℝ U (positionProjection d z)).comp (positionProjection d)+
        (kineticBilinear d m+(kineticBilinear d m).flip) z := by
    change fderiv ℝ ((U ∘ positionProjection d)+(fun x => kineticBilinear d m x x)) z=_
    rw [fderiv_add (hU.comp (positionProjection d).differentiable).differentiableAt hq.differentiableAt,
      ((hU (positionProjection d z)).hasFDerivAt.comp z (positionProjection d).hasFDerivAt).fderiv,
      quadratic_fderiv]
  rw [hf]
  obtain ⟨hqq,hqv,hvq,hvv⟩ := phase_projection_basis i
  constructor
  · change fderiv ℝ U (positionProjection d z) (positionProjection d (Pi.single (Fin.castAdd d i) 1))+
      (kineticBilinear d m z (Pi.single (Fin.castAdd d i) 1)+kineticBilinear d m (Pi.single (Fin.castAdd d i) 1) z)=_
    simp only [hqq,kinetic_bilinear_apply,hvq,Pi.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  · change fderiv ℝ U (positionProjection d z) (positionProjection d (Pi.single (Fin.natAdd d i) 1))+
      (kineticBilinear d m z (Pi.single (Fin.natAdd d i) 1)+kineticBilinear d m (Pi.single (Fin.natAdd d i) 1) z)=_
    simp only [hqv,map_zero,kinetic_bilinear_apply,hvv,zero_add]
    simp [Pi.single_apply]
    ring

end
end Asakura.Chapter8
