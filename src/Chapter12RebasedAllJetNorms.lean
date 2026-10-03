import Chapter12GaussianAllJetNorm
import Chapter12GaussianSingleJetNorm
import Chapter12CylinderValueEquality

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem rebased_all_jet_norms {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (c d : SmoothCylinder H) {N : ℕ} (f g : GaussianJet N) (e : Fin N → H) (he : Orthonormal ℝ e)
    (hc : c.value P W=ᵐ[P] (f.toCylinder e).value P W)
    (hd : d.value P W=ᵐ[P] (g.toCylinder e).value P W) (k : ℕ) :
    (fun w => ‖(cylinderJetCoordinate H P W S hS hcore p hp c k-
      cylinderJetCoordinate H P W S hS hcore p hp d k) w‖)=ᵐ[P]
      (fun w => Real.sqrt (∑a : Fin k → Fin N,
        ‖iteratedFDeriv ℝ k f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)-
          iteratedFDeriv ℝ k g.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)) := by
  have hce := cylinder_value_equality H P W S hS hcore p hp c (f.toCylinder e) hc
  have hde := cylinder_value_equality H P W S hS hcore p hp d (g.toCylinder e) hd
  rw [scalar_jet_core_unique H P W S hS hcore p q hp hq hdense c (f.toCylinder e) hce k,
    scalar_jet_core_unique H P W S hS hcore p q hp hq hdense d (g.toCylinder e) hde k]
  exact gaussian_all_jet_difference_norm H P W S hS hcore p q hp hq hdense f g e he k
theorem rebased_single_jet_norm {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (c : SmoothCylinder H) {N : ℕ} (f : GaussianJet N) (e : Fin N → H) (he : Orthonormal ℝ e)
    (hc : c.value P W=ᵐ[P] (f.toCylinder e).value P W)
    (k : ℕ) :
    (fun w => ‖(cylinderJetCoordinate H P W S hS hcore p hp c k) w‖)=ᵐ[P]
      (fun w => Real.sqrt (∑a : Fin k → Fin N,
        ‖iteratedFDeriv ℝ k f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)) := by
  have hce := cylinder_value_equality H P W S hS hcore p hp c (f.toCylinder e) hc
  rw [scalar_jet_core_unique H P W S hS hcore p q hp hq hdense c (f.toCylinder e) hce k]
  exact gaussian_all_jet_norm H P W S hS hcore p q hp hq hdense f e he k
end Asakura.Chapter12
#print axioms Asakura.Chapter12.rebased_all_jet_norms

#print axioms Asakura.Chapter12.rebased_single_jet_norm
