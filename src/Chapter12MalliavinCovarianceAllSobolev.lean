import Chapter12AllSobolevGradient
import Chapter12AllVectorSobolevInner
import Chapter12AllSobolevMatrixPolynomial

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem malliavin_covariance_all_sobolev {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : I → Lp ℝ 2 P) (U : I → Lp H 2 P)
    (hF : ∀i,HasAllSobolevJets H P W S hS hcore (F i))
    (hDU : ∀i,(F i,U i)∈D.graph) :
    let Γ : Ω → Matrix I I ℝ := fun w i j => inner ℝ (U i w) (U j w)
    (∀i,HasAllVectorSobolevJets H P W S hS hcore (U i)) ∧
    (∀i j,HasAllSobolevJets H P W S hS hcore (fun w => Γ w i j)) ∧
    HasAllSobolevJets H P W S hS hcore (fun w => (Γ w).det) ∧
    ∀i j,HasAllSobolevJets H P W S hS hcore (fun w => (Γ w).adjugate i j) := by
  dsimp only
  have hU i := all_sobolev_gradient H P W S hS hcore D hg (F i) (U i) (hF i) (hDU i)
  have hΓ i j := all_vector_sobolev_inner H P W S hS hcore hdense (U i) (U j) (hU i) (hU j)
  exact ⟨hU,hΓ,all_sobolev_matrix_det H P W S hS hcore hdense _ hΓ,
    all_sobolev_matrix_adjugate H P W S hS hcore hdense _ hΓ⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.malliavin_covariance_all_sobolev
