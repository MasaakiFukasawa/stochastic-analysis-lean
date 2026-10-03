import Chapter12SobolevJetLowerExponent
import Chapter12EvenExponentChoice

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem all_sobolev_from_even {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (F : Ω → ℝ)
    (heven : ∀(n:ℕ) (hn:0<n) (k:ℕ),
      letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
      ∃J : malliavinSobolevJetSpace H P W S hS hcore (2*n:ℕ) (ENNReal.natCast_ne_top _) k,
        (J.val 0 : Ω → ℝ)=ᵐ[P] F) : HasAllSobolevJets H P W S hS hcore F := by
  intro p hp1 hp k
  letI : Fact (1≤p) := ⟨hp1⟩
  obtain ⟨n,hn,hpn,h2n⟩ := even_exponent_dominates p hp
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
  obtain ⟨J,hJ⟩ := heven n hn k
  obtain ⟨K,hK⟩ := sobolev_jet_lower_exponent H P W S hS hcore p (2*n:ℕ) hpn hp (ENNReal.natCast_ne_top _) k J
  exact ⟨K,hK.trans hJ⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_from_even
