import Chapter12CylinderAllSobolevOrders
import Chapter12LpNormLift

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable def cylinderJetSize {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (c : SmoothCylinder H) (k : ℕ) (w : Ω) : ℝ :=
  ∑j : Fin (k+1),‖cylinderJetCoordinate H P W S hS hcore p hp c j.val w‖

noncomputable def cylinderJetDistance {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (c d : SmoothCylinder H) (k : ℕ) (w : Ω) : ℝ :=
  ∑j : Fin (k+1),‖(cylinderJetCoordinate H P W S hS hcore p hp c j.val-
    cylinderJetCoordinate H P W S hS hcore p hp d j.val) w‖

theorem finite_sum_norm_member {I : Type*} [Fintype I] (E : I → Type*)
    [∀i,NormedAddCommGroup (E i)] (x : ∀i,E i) (j : I) : ‖x j‖≤∑i,‖x i‖ :=
  Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ j)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.finite_sum_norm_member
