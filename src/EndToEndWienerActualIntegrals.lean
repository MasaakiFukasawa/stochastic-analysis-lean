import EndToEndWienerInterface

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter12

/-- Keep the connection to the actual coordinate Ito integrals and their
infinite-horizon terminal values when packaging the Wiener interface. -/
theorem independent_wiener_actual_integrals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 2) :
    ∃ I : Asakura.IndependentWienerIntegrals P,
      ∀ f g : Lp ℝ 2 (volume : Measure ℝ),
        let q := singleCoordinateIsometry (0 : Fin 2) (L2Restriction volume (Ioi 0) f) +
          singleCoordinateIsometry (1 : Fin 2) (L2Restriction volume (Ioi 0) g)
        ∃ N : Fin 2 → HalfClosedTime → Ω → ℝ,
        ∃ hN : ∀ i, ContinuousM2Witness P B.F (N i),
          (∀ i, ItoCovarianceFormula P B.F (B.W i) (fun z => q i z.2) (N i)) ∧
          I.first f + I.second g = ∑ i, ((hN i).moment ⊤).toLp (N i ⊤) := by
  obtain ⟨W, hW, hIto⟩ := vector_actual_wiener_isometry_exists P B
  obtain ⟨I, hfirst, hsecond⟩ := wiener_interface_from_isometry P W hW
  refine ⟨I, ?_⟩
  intro f g q
  obtain ⟨N, hN, hcov, hsum⟩ := hIto q
  refine ⟨N, hN, hcov, ?_⟩
  rw [hfirst, hsecond, ← map_add]
  exact hsum

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.independent_wiener_actual_integrals
