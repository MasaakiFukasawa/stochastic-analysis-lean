import Chapter12AllSobolevFiniteAlgebra
import Mathlib.LinearAlgebra.Matrix.Adjugate

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
include hdense

theorem all_sobolev_matrix_det (A:Ω → Matrix I I ℝ)
    (hA:∀i j,HasAllSobolevJets H P W S hS hcore (fun w => A w i j)) :
    HasAllSobolevJets H P W S hS hcore (fun w => (A w).det) := by
  simp_rw [Matrix.det_apply']
  apply all_sobolev_finset_sum H P W S hS hcore
  intro σ _
  apply all_sobolev_smul H P W S hS hcore
  apply all_sobolev_finset_prod H P W S hS hcore hdense
  intro i _
  exact hA (σ i) i

theorem all_sobolev_matrix_adjugate (A:Ω → Matrix I I ℝ)
    (hA:∀i j,HasAllSobolevJets H P W S hS hcore (fun w => A w i j)) (i j:I) :
    HasAllSobolevJets H P W S hS hcore (fun w => (A w).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply all_sobolev_matrix_det H P W S hS hcore hdense
  intro a b
  by_cases h:a=j
  · subst a
    simpa using all_sobolev_const H P W S hS hcore ((Pi.single i (1:ℝ) : I → ℝ) b)
  · simpa [Matrix.updateRow,Function.update_of_ne h] using hA a b
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_matrix_det
#print axioms Asakura.Chapter12.all_sobolev_matrix_adjugate
