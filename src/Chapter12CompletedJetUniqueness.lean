import Chapter12ScalarJetOperatorsFromCore
import Chapter12DivergenceAllSobolev

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

variable {Ω:Type*} [MeasurableSpace Ω]
    (H:RealHilbertSpaceData) [Nontrivial H] (P:Measure Ω) [IsProbabilityMeasure P]
    (W:H →ₗᵢ[ℝ] Lp ℝ 2 P) (S:Set H) (hS:Dense S)
    (hcore:∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q:ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp:p≠⊤) (hq:q≠⊤)
    (hdense:DenseRange (fun c:SmoothCylinder H => c.valueLp P W S hS hcore q hq))
include hdense

theorem completed_scalar_jet_value_injective (k:ℕ) :
    Function.Injective (fun x:malliavinSobolevJetSpace H P W S hS hcore p hp k => x.val 0) := by
  obtain ⟨D,hD,hjet⟩ := scalar_jet_operators_from_core H P W S hS hcore p q hp hq hdense
  let E:Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  let jet := fun c:SmoothCylinder H => WithLp.toLp p
    ((fun j:Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀j,E j)
  exact (sobolev_jet_completion p E (fun j:Fin k => D j.val) (fun j => hD j.val)
    jet (fun c j => hjet c j.val)).2.1

theorem completed_vector_jet_value_injective (k:ℕ) :
    Function.Injective (fun x:vectorSobolevJetSpace H P W S hS hcore p hp k => x.val 0) := by
  obtain ⟨D,hD,hjet⟩ := higher_vector_core_operators H P W S hS hcore p q hp hq hdense
  let E:Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) p P
  exact (sobolev_jet_completion 1 E (fun j:Fin k => D j.val) (fun j => hD j.val)
    (vectorSobolevCoreJet H P W S hS hcore p hp k)
    (fun c j => hjet j.val (iteratedVectorCylinderExpr H c j.val))).2.1
end Asakura.Chapter12
#print axioms Asakura.Chapter12.completed_scalar_jet_value_injective
#print axioms Asakura.Chapter12.completed_vector_jet_value_injective
