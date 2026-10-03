import Chapter12VectorSobolevJetCore
import Chapter12CylinderJetSizeMonotone

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
variable {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)

noncomputable def vectorJetSize (c:VectorCylinderExpr H H) (k:ℕ) (w:Ω) : ℝ :=
  ∑j:Fin (k+1),‖(iteratedVectorCylinderExpr H c j.val).valueLp P W S hS hcore p hp w‖

noncomputable def vectorJetDistance (c d:VectorCylinderExpr H H) (k:ℕ) (w:Ω) : ℝ :=
  ∑j:Fin (k+1),‖((iteratedVectorCylinderExpr H c j.val).valueLp P W S hS hcore p hp-
    (iteratedVectorCylinderExpr H d j.val).valueLp P W S hS hcore p hp) w‖

theorem vectorJetSize_mono (c:VectorCylinderExpr H H) {j k:ℕ} (hjk:j≤k) (w:Ω) :
    vectorJetSize H P W S hS hcore p hp c j w≤vectorJetSize H P W S hS hcore p hp c k w :=
  finite_prefix_sum_mono (fun i => ‖(iteratedVectorCylinderExpr H c i).valueLp P W S hS hcore p hp w‖)
    (fun _ => norm_nonneg _) hjk

theorem vectorJetDistance_mono (c d:VectorCylinderExpr H H) {j k:ℕ} (hjk:j≤k) (w:Ω) :
    vectorJetDistance H P W S hS hcore p hp c d j w≤vectorJetDistance H P W S hS hcore p hp c d k w :=
  finite_prefix_sum_mono (fun i => ‖((iteratedVectorCylinderExpr H c i).valueLp P W S hS hcore p hp-
    (iteratedVectorCylinderExpr H d i).valueLp P W S hS hcore p hp) w‖) (fun _ => norm_nonneg _) hjk
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vectorJetDistance_mono
