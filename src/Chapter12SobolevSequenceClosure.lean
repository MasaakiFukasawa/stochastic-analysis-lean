import Chapter12CompletedScalarJetLimit

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

variable {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)

theorem scalar_even_jet_cauchy_zero (F:ℕ → Ω → ℝ)
    (hzero:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
      (v:ℕ → Lp ℝ p P), (∀m,(v m:Ω → ℝ)=ᵐ[P] F m) → CauchySeq v) :
    ScalarEvenJetCauchy H P W S hS hcore F 0 := by
  intro n hn hp1 x hx
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨hp1⟩
  have hz := hzero (2*n:ℕ) (ENNReal.natCast_ne_top _) (fun m => (x m).val 0) hx
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hz
  let E:Fin 1 → Type _ := fun j => Lp (malliavinTensorOrder H j.val) (2*n:ℕ) P
  let v : ∀j:Fin 1,E j := fun j => by
    have he:j=0 := Subsingleton.elim _ _
    subst j
    exact z
  have hcoord:∀j:Fin 1,Tendsto (fun m => (x m).val j) atTop (𝓝 (v j)) := by
    intro j
    fin_cases j
    exact hz
  exact (((PiLp.continuous_toLp 1 E).tendsto v).comp
    (tendsto_pi_nhds.mpr hcoord)).cauchySeq

theorem all_sobolev_sequence_closed (F:ℕ → Ω → ℝ) (G:Ω → ℝ)
    (hF:∀m,HasAllSobolevJets H P W S hS hcore (F m))
    (hc:∀k,ScalarEvenJetCauchy H P W S hS hcore F k)
    (hG:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤),MemLp G p P)
    (ht:∀(p:ℝ≥0∞) [Fact (1≤p)] (hp:p≠⊤)
      (v:ℕ → Lp ℝ p P), (∀m,(v m:Ω → ℝ)=ᵐ[P] F m) →
        Tendsto v atTop (𝓝 ((hG p hp).toLp G))) :
    HasAllSobolevJets H P W S hS hcore G := by
  apply all_sobolev_from_even H P W S hS hcore
  intro n hn k
  let p:ℝ≥0∞ := (2*n:ℕ)
  have hp1:1≤p := by dsimp [p];exact_mod_cast (show 1≤2*n by omega)
  letI:Fact (1≤p) := ⟨hp1⟩
  have hp:p≠⊤ := ENNReal.natCast_ne_top _
  have hex:∀m,∃x:malliavinSobolevJetSpace H P W S hS hcore p hp k,
      (x.val 0:Ω → ℝ)=ᵐ[P] F m := fun m => hF m p hp1 hp k
  choose x hx using hex
  obtain ⟨y,hy⟩ := completed_scalar_jet_cauchy_limit H P W S hS hcore p hp k x (hc k n hn hp1 x hx)
  let E:Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  have hy0:Tendsto (fun m => (x m).val 0) atTop (𝓝 (y.val 0)) :=
    (((continuous_apply (0:Fin (k+1))).comp (PiLp.continuous_ofLp 1 E)).tendsto _).comp hy
  have he:y.val 0=(hG p hp).toLp G := tendsto_nhds_unique hy0 (ht p hp _ hx)
  refine ⟨y,?_⟩
  rw [he]
  exact (hG p hp).coeFn_toLp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_sequence_closed
