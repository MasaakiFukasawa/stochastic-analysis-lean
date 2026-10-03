import FullAuditL1Identification

open MeasureTheory Set
namespace Asakura.Chapter1Complete

/-- The operator obtained by the manuscript's dense extension is identified
with the conditional expectation used in all downstream Lean statements. -/
theorem constructed_L1_operator_is_condExp {Ω : Type*} {m m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m≤m0) :
    ∃ L : Lp ℝ 1 P →L[ℝ] Lp ℝ 1 P,
      (∀ X : Asakura.FullAudit.squareIntegrableDomain P,
        L X=Asakura.FullAudit.l2ProjectionOnL1Domain P hm X) ∧
      ∀ X : Lp ℝ 1 P,(L X : Ω → ℝ)=ᵐ[P] P[(X : Ω → ℝ) | m] := by
  obtain ⟨L,he,hmL,hchar⟩ := Asakura.FullAudit.l1_conditional_operator_written P hm
  refine ⟨L,he,?_⟩
  intro X
  exact ae_eq_condExp_of_forall_setIntegral_eq hm (L1.integrable_coeFn X)
    (fun _ _ _ => (L1.integrable_coeFn (L X)).integrableOn)
    (fun A hA _ => (hchar X (L X) (hmL X)).mp rfl A hA) (hmL X)

end Asakura.Chapter1Complete
