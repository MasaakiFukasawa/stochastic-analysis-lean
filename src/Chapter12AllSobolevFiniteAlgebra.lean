import Chapter12AllSobolevProduct
import Chapter12GaussianJetProducts

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)

theorem all_sobolev_const (a:ℝ) : HasAllSobolevJets H P W S hS hcore (fun _:Ω => a) := by
  apply cylinder_all_sobolev_orders H P W S hS hcore ((GaussianJet.constant 0 a).toCylinder Fin.elim0)
  exact Filter.EventuallyEq.rfl

theorem all_sobolev_finset_sum {I:Type*} (s:Finset I) (F:I → Ω → ℝ)
    (hF:∀i∈s,HasAllSobolevJets H P W S hS hcore (F i)) :
    HasAllSobolevJets H P W S hS hcore (fun w => ∑i∈s,F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using all_sobolev_const H P W S hS hcore 0
  | @insert a s ha ih =>
    have hh := all_sobolev_add H P W S hS hcore (F a) (fun w => ∑i∈s,F i w)
      (hF a (Finset.mem_insert_self _ _)) (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.sum_insert ha] using hh

theorem all_sobolev_finset_prod
    (hdense : ∀ (q : ℝ≥0∞) [Fact (1≤q)] (hq : q≠⊤),
      DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    {I:Type*} (s:Finset I) (F:I → Ω → ℝ)
    (hF:∀i∈s,HasAllSobolevJets H P W S hS hcore (F i)) :
    HasAllSobolevJets H P W S hS hcore (fun w => ∏i∈s,F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using all_sobolev_const H P W S hS hcore 1
  | @insert a s ha ih =>
    have hh := all_sobolev_product H P W S hS hcore hdense (F a) (fun w => ∏i∈s,F i w)
      (hF a (Finset.mem_insert_self _ _)) (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))
    simpa only [Finset.prod_insert ha] using hh
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_finset_prod
