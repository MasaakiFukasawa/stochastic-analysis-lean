import Chapter12CylinderCompositionUniformEstimate
import Chapter12FiniteJetPolynomialCauchy
import Chapter12ScalarSobolevSumJet

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem cylinder_composition_cauchy {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b)
    (hB : ∀j:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ j b x‖≤C*(1+‖x‖)^a)
    (k : ℕ) (K : ℝ) (hK : 0≤K) (a : ℕ)
    (hKB : ∀j≤k+1,∀x,‖iteratedFDeriv ℝ j b x‖≤K*(1+‖x‖)^a)
    (p q t s : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [Fact (1≤t)] [Fact (1≤s)]
    [Fact (1≤t*(a+k+1:ℕ))] [HolderConjugate p q] [HolderConjugate (t*(a+k+1:ℕ)) s]
    [HolderTriple t t p]
    (hp : p≠⊤) (hq : q≠⊤) (hr : t*(a+k+1:ℕ)≠⊤) (hs : s≠⊤)
    (hdq : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (hds : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore s hs))
    (c : ℕ → SmoothCylinder H)
    (hc : CauchySeq (fun n => scalarSobolevSumCoreJet H P W S hS hcore (t*(a+k+1:ℕ)) hr k (c n))) :
    ∀j:Fin (k+1),CauchySeq (fun n => cylinderJetCoordinate H P W S hS hcore p hp
      (composeSmoothCylinder (c n) b hb hB) j.val) := by
  intro j
  obtain ⟨C,hC,hest⟩ := cylinder_composition_uniform_estimate H P W S hS hcore
    p q (t*(a+k+1:ℕ)) s hp hq hr hs hdq hds b hb hB k K hK a hKB j.val (by omega)
  apply finite_jet_polynomial_cauchy (fun i:Fin (k+1) => malliavinTensorOrder H i.val)
    P p t (a+k+1) (by omega) _ _ hc C hC
  intro n m
  exact hest (c n) (c m)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_composition_cauchy
