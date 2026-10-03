import Chapter12HigherSobolevCompatibility
import Chapter12CylinderAllSobolevOrders

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_jet_lower_exponent {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤)
    (k : ℕ) (y : malliavinSobolevJetSpace H P W S hS hcore q hq k) :
    ∃x : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      (x.val 0 : Ω → ℝ)=ᵐ[P] (y.val 0 : Ω → ℝ) := by
  obtain ⟨L,hL,hmap⟩ := higher_sobolev_exponent_compatibility H P W S hS hcore p q hpq hp hq k
  refine ⟨⟨L y.val,hmap y.val y.property⟩,?_⟩
  change (L y.val 0 : Ω → ℝ)=ᵐ[P] (y.val 0 : Ω → ℝ)
  rw [hL]
  exact probabilityLpInclusion_coe P p q hpq (y.val 0)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_jet_lower_exponent
