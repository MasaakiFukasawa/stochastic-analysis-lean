import Chapter12AllVectorSobolevLinear

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem all_vector_sobolev_finset_sum {Ω I:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u:Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (s:Finset I) (U:I → Ω → H)
    (hU:∀i∈s,HasAllVectorSobolevJets H P W S hS hcore (U i)) :
    HasAllVectorSobolevJets H P W S hS hcore (fun w => ∑i∈s,U i w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro p hp1 hp k
    letI:Fact (1≤p) := ⟨hp1⟩
    refine ⟨0,?_⟩
    change ((0:Lp H p P):Ω → H)=ᵐ[P] _
    filter_upwards [Lp.coeFn_zero H p P] with w hw
    simpa using hw
  | @insert a s ha ih =>
    have hh := all_vector_sobolev_add H P W S hS hcore (U a) (fun w => ∑i∈s,U i w)
      (hU a (Finset.mem_insert_self _ _)) (ih (fun i hi => hU i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.sum_insert ha] using hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_vector_sobolev_finset_sum
