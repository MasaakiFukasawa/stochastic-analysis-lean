import Chapter12GaussianClosedDerivativeDifference
import Chapter12ScalarJetOperatorsFromCore
import Chapter12LpAffineNormBound

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem rebased_derivative_path_bound {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (c d : SmoothCylinder H) {N : ℕ} (f g : GaussianJet N)
    (e : Fin N → H) (he : Orthonormal ℝ e)
    (hc : c.valueLp P W S hS hcore p hp=(f.toCylinder e).valueLp P W S hS hcore p hp)
    (hd : d.valueLp P W S hS hcore p hp=(g.toCylinder e).valueLp P W S hS hcore p hp)
    (k : ℕ) {E : Type*} [NormedAddCommGroup E]
    (V : Lp E p P) (C r : ℝ) (hC : 0≤C) (hr : 0≤r)
    (hb : ∀ᵐw ∂P,Real.sqrt (∑a : Fin (k+1) → Fin N,
      ‖iteratedFDeriv ℝ (k+1) f.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)-
        iteratedFDeriv ℝ (k+1) g.f (fun i => W (e i) w) (fun i => Pi.single (a i) 1)‖^2)≤C*(‖V w‖+r)) :
    ‖cylinderJetCoordinate H P W S hS hcore p hp c (k+1)-
      cylinderJetCoordinate H P W S hS hcore p hp d (k+1)‖≤C*(‖V‖+r) := by
  rw [scalar_jet_core_unique H P W S hS hcore p q hp hq hdense c (f.toCylinder e) hc (k+1),
    scalar_jet_core_unique H P W S hS hcore p q hp hq hdense d (g.toCylinder e) hd (k+1)]
  obtain ⟨D,hclosed,hD⟩ := higher_vector_core_operators H P W S hS hcore p q hp hq hdense
  apply lp_affine_norm_bound P p _ V C r hC hr
  filter_upwards [gaussian_closed_derivative_difference H P W S hS hcore p hp f g e he D hD k,hb] with w hw hbw
  exact hw.le.trans hbw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.rebased_derivative_path_bound
