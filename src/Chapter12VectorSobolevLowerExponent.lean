import Chapter12DivergenceAllSobolev

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem vector_sobolev_lower_exponent {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q:ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq:p≤q) (hp:p≠⊤) (hq:q≠⊤)
    (k:ℕ) (x:vectorSobolevJetSpace H P W S hS hcore q hq k) :
    ∃y:vectorSobolevJetSpace H P W S hS hcore p hp k,
      (y.val 0 : Ω → H)=ᵐ[P] (x.val 0 : Ω → H) := by
  let E:Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) q P
  let F:Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) p P
  obtain ⟨L,hL,hmap⟩ := jet_completion_map 1 1 E F (fun _ => probabilityLpInclusion P p q hpq)
    (vectorSobolevCoreJet H P W S hS hcore q hq k) (vectorSobolevCoreJet H P W S hS hcore p hp k)
    (fun c j => vector_cylinder_exponent P W S hS hcore p q hpq hp hq (iteratedVectorCylinderExpr H c j.val))
  refine ⟨⟨L x.val,hmap x.val x.property⟩,?_⟩
  change (L x.val 0 : Ω → H)=ᵐ[P] (x.val 0 : Ω → H)
  rw [hL]
  exact probabilityLpInclusion_coe P p q hpq (x.val 0)

theorem all_vector_sobolev_from_even {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (U:Ω → H)
    (heven:∀(n:ℕ) (hn:0<n) (k:ℕ),
      letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
      ∃J:vectorSobolevJetSpace H P W S hS hcore (2*n:ℕ) (ENNReal.natCast_ne_top _) k,
        (J.val 0 : Ω → H)=ᵐ[P] U) : HasAllVectorSobolevJets H P W S hS hcore U := by
  intro p hp1 hp k
  letI : Fact (1≤p) := ⟨hp1⟩
  obtain ⟨n,hn,hpn,h2n⟩ := even_exponent_dominates p hp
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
  obtain ⟨J,hJ⟩ := heven n hn k
  obtain ⟨K,hK⟩ := vector_sobolev_lower_exponent H P W S hS hcore p (2*n:ℕ) hpn hp (ENNReal.natCast_ne_top _) k J
  exact ⟨K,hK.trans hJ⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_vector_sobolev_from_even
