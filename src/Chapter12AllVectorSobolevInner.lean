import Chapter12AllVectorSobolevNormSquare
import Chapter12AllVectorSobolevLinear
import Chapter12AllSobolevLinear

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem all_vector_sobolev_inner {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (U V : Ω → H) (hU : HasAllVectorSobolevJets H P W S hS hcore U)
    (hV : HasAllVectorSobolevJets H P W S hS hcore V) :
    HasAllSobolevJets H P W S hS hcore (fun w => inner ℝ (U w) (V w)) := by
  have hsum := all_vector_sobolev_norm_square H P W S hS hcore hdense _
    (all_vector_sobolev_add H P W S hS hcore U V hU hV)
  have hU2 := all_vector_sobolev_norm_square H P W S hS hcore hdense U hU
  have hV2 := all_vector_sobolev_norm_square H P W S hS hcore hdense V hV
  have hx := all_sobolev_smul H P W S hS hcore _
    (all_sobolev_add H P W S hS hcore _ _
      (all_sobolev_add H P W S hS hcore _ _ hsum (all_sobolev_smul H P W S hS hcore _ hU2 (-1)))
      (all_sobolev_smul H P W S hS hcore _ hV2 (-1))) (1/2)
  apply all_sobolev_congr H P W S hS hcore _ _ hx
  exact Filter.Eventually.of_forall (fun w => by nlinarith [norm_add_sq_real (U w) (V w)])
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_vector_sobolev_inner
