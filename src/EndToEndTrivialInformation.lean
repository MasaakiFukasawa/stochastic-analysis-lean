import Chapter13BondNumeraire

open MeasureTheory Set
namespace Asakura.EndToEnd

/-- Trivial information means probability zero or one, not literal equality
of the sigma algebra with bottom; completion does not cause a gap. -/
theorem conditional_of_zero_one {Ω : Type*} {G m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hle : G ≤ m)
    (hG : ∀ A, MeasurableSet[G] A → P A = 0 ∨ P A = 1)
    (Z : Ω → ℝ) (hZ : Integrable Z P) :
    P[Z|G] =ᵐ[P] (fun _ => ∫ ω, Z ω ∂P) := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hZ
  · intro s hs hfin
    exact (integrable_const _).integrableOn
  · intro s hs hfin
    rcases hG s hs with hzero | hone
    · simp [Measure.restrict_eq_zero.mpr hzero]
    · have hae : s ∈ ae P := mem_ae_iff.mpr ((prob_compl_eq_zero_iff (hle s hs)).mpr hone)
      rw [← integral_eq_setIntegral hae, ← integral_eq_setIntegral hae]
      simp
  · exact stronglyMeasurable_const.aestronglyMeasurable

#print axioms conditional_of_zero_one
end Asakura.EndToEnd
