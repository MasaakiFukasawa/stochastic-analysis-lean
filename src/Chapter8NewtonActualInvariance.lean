import Chapter8GibbsSkewManuscript
import Chapter8NewtonMobility
import Chapter8HamiltonianIntegrability

open MeasureTheory Set
open scoped NNReal BigOperators ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

/-- Actual Newton SDE construction and invariance of its phase Gibbs
density. Product identification with Gibbs times Maxwell is a separate step. -/
theorem newton_actual_invariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (U : (Fin d → ℝ) → ℝ) (hU : ContDiff ℝ 3 U)
    (A₂ A₃ : ℝ≥0)
    (h₂ : ∀ x,‖fderiv ℝ (fderiv ℝ U) x‖≤(A₂:ℝ))
    (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ))
    (β m γ : ℝ) (hβ : 0<β) (hm : 0<m) (hγ : 0<γ)
    (hi : Integrable (fun x : Fin d → ℝ => (1+∑ i,x i^2)*Real.exp (-β*U x))) :
    let H := newtonHamiltonian U m
    let π := volume.withDensity (fun x : Fin (d+d) → ℝ =>
      ENNReal.ofReal ((∫ y : Fin (d+d) → ℝ,Real.exp (-β*H y))⁻¹*Real.exp (-β*H x)))
    let b := Fin.addCases (fun i z => velocityProjection d z i)
      (fun i z => -(fderiv ℝ U (positionProjection d z) (Pi.single i 1)+γ*velocityProjection d z i)/m)
    IsProbabilityMeasure π ∧
    ∃ Z : (Fin (d+d) → ℝ) → HalfClosedTime → Ω → Fin (d+d) → ℝ,
      (∀ x,VectorSDESolution P B.F B.W b
        (fun i j _ => newtonNoise d (Real.sqrt (2*γ*β⁻¹)/m) i j) (fun _ => x) (Z x)) ∧
      ∀ T : ℝ,0≤T → ∃ Y : (Fin (d+d) → ℝ) × Ω → (Fin (d+d) → ℝ),Measurable Y ∧
        (∀ x,(fun w => Y (x,w))=ᵐ[P] Z x (realTimeClamp T)) ∧ (π.prod P).map Y=π := by
  obtain ⟨hH,C₂,C₃,hC₂,hC₃⟩ := newton_hamiltonian_regularity U hU A₂ A₃ h₂ h₃ m
  have hsq : (Real.sqrt (2*γ*β⁻¹)/m)^2=2*β⁻¹*γ/m^2 := by
    rw [div_pow,Real.sq_sqrt (by positivity)]
    ring
  have hh := gibbs_skew_manuscript_invariance P B (newtonHamiltonian U m) hH C₂ C₃ hC₂ hC₃ β hβ
    (newton_hamiltonian_integrability U hU.continuous β m hβ hm hi)
    (newtonMobility d m γ) (newtonNoise d (Real.sqrt (2*γ*β⁻¹)/m))
    (newton_einstein_blocks d m γ β _ hsq)
  have he : (fun i z => -(∑ j,newtonMobility d m γ i j*fderiv ℝ (newtonHamiltonian U m) z (Pi.single j 1)))=
      Fin.addCases (fun i z => velocityProjection d z i)
        (fun i z => -(fderiv ℝ U (positionProjection d z) (Pi.single i 1)+γ*velocityProjection d z i)/m) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> funext z
    · simpa only [Fin.addCases_left,Fin.addCases_right] using (newton_drift_blocks U (hU.differentiable (by norm_num)) m γ hm.ne' z i).1
    · simpa only [Fin.addCases_left,Fin.addCases_right] using (newton_drift_blocks U (hU.differentiable (by norm_num)) m γ hm.ne' z i).2
  rw [he] at hh
  exact hh

end Asakura.Chapter8
