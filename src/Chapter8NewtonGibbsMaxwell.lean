import Chapter8NewtonActualInvariance
import Chapter8HamiltonianProductLaw
import Chapter8MaxwellDensity

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace Asakura.Chapter8
open Asakura.Chapter4 Asakura.Chapter3Complete Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's Newton invariant distribution is exactly the product
of the position Gibbs measure and the centered Maxwell Gaussian velocity law. -/
theorem newton_gibbs_maxwell_manuscript {Ω : Type*} [MeasurableSpace Ω]
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
      π.map (phaseMeasurableEquiv d)=
        (volume.withDensity (fun q : Fin d → ℝ => ENNReal.ofReal
          ((∫ y : Fin d → ℝ,Real.exp (-β*U y))⁻¹*Real.exp (-β*U q)))).prod
        (Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨(β*m)⁻¹,by positivity⟩)) ∧
    ∃ Z : (Fin (d+d) → ℝ) → HalfClosedTime → Ω → Fin (d+d) → ℝ,
      (∀ x,VectorSDESolution P B.F B.W b
        (fun i j _ => newtonNoise d (Real.sqrt (2*γ*β⁻¹)/m) i j) (fun _ => x) (Z x)) ∧
      ∀ T : ℝ,0≤T → ∃ Y : (Fin (d+d) → ℝ) × Ω → (Fin (d+d) → ℝ),Measurable Y ∧
        (∀ x,(fun w => Y (x,w))=ᵐ[P] Z x (realTimeClamp T)) ∧ (π.prod P).map Y=π := by
  obtain ⟨hp,Z,hZ,hinv⟩ := newton_actual_invariance P B U hU A₂ A₃ h₂ h₃ β m γ hβ hm hγ hi
  refine ⟨hp,?_,Z,hZ,hinv⟩
  rw [hamiltonian_product_law U hU.continuous β m,maxwell_density d β m hβ hm]

end Asakura.Chapter8
