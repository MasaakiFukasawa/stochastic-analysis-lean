import EndToEndWienerActualIntegrals
import Chapter2M2TimeContinuity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Both scalar integrals and their L2 limits at infinity are exposed. -/
theorem independent_wiener_two_ito_integrals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 2) :
    ∃ I : Asakura.IndependentWienerIntegrals P,
      ∀ f g : Lp ℝ 2 (volume : Measure ℝ),
        ∃ N : Fin 2 → HalfClosedTime → Ω → ℝ,
        ∃ hN : ∀ i, ContinuousM2Witness P B.F (N i),
          ItoCovarianceFormula P B.F (B.W 0)
            (fun z => L2Restriction volume (Ioi 0) f z.2) (N 0) ∧
          ItoCovarianceFormula P B.F (B.W 1)
            (fun z => L2Restriction volume (Ioi 0) g z.2) (N 1) ∧
          I.first f + I.second g =
            ((hN 0).moment ⊤).toLp (N 0 ⊤) + ((hN 1).moment ⊤).toLp (N 1 ⊤) ∧
          (∀ i, Tendsto (fun t => eLpNorm (N i t - N i ⊤) 2 P)
            (𝓝[<] (⊤ : HalfClosedTime)) (𝓝 0)) := by
  obtain ⟨I,hI⟩ := independent_wiener_actual_integrals P B
  refine ⟨I,?_⟩
  intro f g
  obtain ⟨N,hN,hcov,hsum⟩ := hI f g
  refine ⟨N,hN,?_,?_,?_,?_⟩
  · have h := hcov 0
    simpa [singleCoordinateIsometry, PiLp.add_apply, Pi.single_apply] using h
  · have h := hcov 1
    simpa [singleCoordinateIsometry, PiLp.add_apply, Pi.single_apply] using h
  · simpa only [Fin.sum_univ_two] using hsum
  · intro i
    exact terminal_l2_limit_all_times P B.F B.mono B.le (N i) (N i) (hN i)
      (fun _ _ => EventuallyEq.rfl)

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.independent_wiener_two_ito_integrals
