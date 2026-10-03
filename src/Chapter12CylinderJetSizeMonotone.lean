import Chapter12CylinderJetSize

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12

theorem finite_prefix_sum_mono (f : ℕ → ℝ) (hf : ∀j,0≤f j) {j k : ℕ} (hjk : j≤k) :
    (∑i:Fin (j+1),f i.val)≤∑i:Fin (k+1),f i.val := by
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hjk 1))
    (fun i _ _ => hf i)

theorem cylinderJetSize_mono {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (c : SmoothCylinder H) {j k : ℕ} (hjk : j≤k) (w : Ω) :
    cylinderJetSize H P W S hS hcore p hp c j w≤cylinderJetSize H P W S hS hcore p hp c k w :=
  finite_prefix_sum_mono (fun i => ‖cylinderJetCoordinate H P W S hS hcore p hp c i w‖)
    (fun _ => norm_nonneg _) hjk

theorem cylinderJetDistance_mono {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (c d : SmoothCylinder H) {j k : ℕ} (hjk : j≤k) (w : Ω) :
    cylinderJetDistance H P W S hS hcore p hp c d j w≤cylinderJetDistance H P W S hS hcore p hp c d k w :=
  finite_prefix_sum_mono (fun i => ‖(cylinderJetCoordinate H P W S hS hcore p hp c i-
    cylinderJetCoordinate H P W S hS hcore p hp d i) w‖) (fun _ => norm_nonneg _) hjk
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinderJetDistance_mono
