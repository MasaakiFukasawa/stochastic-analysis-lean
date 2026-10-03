import EndToEndBondApplications

open MeasureTheory Set
open scoped NNReal
namespace Asakura.EndToEnd

/-- Initial information remains trivial after an absolutely continuous
change of probability, even when it is completed by null sets. -/
theorem zero_one_information_transfer {Ω : Type*} {G m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hG : G ≤ m) (hQP : Q ≪ P)
    (hzero : ∀ A, MeasurableSet[G] A → P A = 0 ∨ P A = 1) :
    ∀ A, MeasurableSet[G] A → Q A = 0 ∨ Q A = 1 := by
  intro A hA
  rcases hzero A hA with h | h
  · exact Or.inl (hQP h)
  · exact Or.inr ((prob_compl_eq_zero_iff (hG A hA)).mp
      (hQP ((prob_compl_eq_zero_iff (hG A hA)).mpr h)))

theorem bond_initial_price_under_risk_neutral_measure
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (M : BondMarket Q) (hQP : Q ≪ P)
    (hzero : ∀ A, MeasurableSet[M.F 0] A → P A = 0 ∨ P A = 1)
    (hbank : ∀ ω, M.bank 0 ω = 1) (u : ℝ≥0) :
    M.bond u 0 =ᵐ[Q] (fun _ => ∫ ω, (M.bank u ω)⁻¹ ∂Q) :=
  M.initial_price (zero_one_information_transfer P Q (M.le 0) hQP hzero) hbank u

#print axioms zero_one_information_transfer
#print axioms bond_initial_price_under_risk_neutral_measure
end Asakura.EndToEnd
