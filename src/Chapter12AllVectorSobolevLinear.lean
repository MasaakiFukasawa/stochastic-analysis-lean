import Chapter12DivergenceAllSobolev

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)

theorem all_vector_sobolev_congr (F G : Ω → H) (hF : HasAllVectorSobolevJets H P W S hS hcore F)
    (hFG : F=ᵐ[P] G) : HasAllVectorSobolevJets H P W S hS hcore G := by
  intro p hp1 hp k
  obtain ⟨x,hx⟩ := hF p hp1 hp k
  exact ⟨x,hx.trans hFG⟩

theorem all_vector_sobolev_add (F G : Ω → H) (hF : HasAllVectorSobolevJets H P W S hS hcore F)
    (hG : HasAllVectorSobolevJets H P W S hS hcore G) :
    HasAllVectorSobolevJets H P W S hS hcore (fun w => F w+G w) := by
  intro p hp1 hp k
  letI : Fact (1≤p) := ⟨hp1⟩
  obtain ⟨x,hx⟩ := hF p hp1 hp k
  obtain ⟨y,hy⟩ := hG p hp1 hp k
  refine ⟨x+y,?_⟩
  change ((x.val 0+y.val 0) : Ω → H)=ᵐ[P] (fun w => F w+G w)
  filter_upwards [hx,hy,Lp.coeFn_add (x.val 0) (y.val 0)] with w hw hz ha
  rw [ha,Pi.add_apply,hw,hz]

theorem all_vector_sobolev_smul (F : Ω → H) (hF : HasAllVectorSobolevJets H P W S hS hcore F) (c : ℝ) :
    HasAllVectorSobolevJets H P W S hS hcore (fun w => c • F w) := by
  intro p hp1 hp k
  letI : Fact (1≤p) := ⟨hp1⟩
  obtain ⟨x,hx⟩ := hF p hp1 hp k
  refine ⟨c • x,?_⟩
  change ((c • x.val 0) : Ω → H)=ᵐ[P] (fun w => c • F w)
  filter_upwards [hx,Lp.coeFn_smul c (x.val 0)] with w hw ha
  rw [ha,Pi.smul_apply,hw]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_vector_sobolev_add
#print axioms Asakura.Chapter12.all_vector_sobolev_smul
