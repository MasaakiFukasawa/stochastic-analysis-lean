import EndToEndWienerActualIntegrals
import MandelbrotVanNess

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace Asakura.EndToEnd
open Asakura Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter12

/-- The MVN result with actual Ito-integral witnesses retained. The separate
conversion from two independent Brownian motions to BrownianSystem is not
asserted by this theorem. -/
theorem mandelbrot_van_ness_from_brownian_system
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : BrownianSystem P 2)
    (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) :
    ∃ I : IndependentWienerIntegrals P,
      (∀ f g : Lp ℝ 2 (volume : Measure ℝ),
        let q := singleCoordinateIsometry (0 : Fin 2) (L2Restriction volume (Ioi 0) f) +
          singleCoordinateIsometry (1 : Fin 2) (L2Restriction volume (Ioi 0) g)
        ∃ N : Fin 2 → HalfClosedTime → Ω → ℝ,
        ∃ hN : ∀ i, ContinuousM2Witness P B.F (N i),
          (∀ i, ItoCovarianceFormula P B.F (B.W i) (fun z => q i z.2) (N i)) ∧
          I.first f + I.second g = ∑ i, ((hN i).moment ⊤).toLp (N i ⊤)) ∧
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧ (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ t, Y t =ᵐ[P] (mvnProcessLp I H hH0 hH1 t : Ω → ℝ)) ∧
      IsGaussianProcess Y P ∧ (∀ t, (∫ ω, Y t ω ∂P) = 0) ∧
      (∀ s t, (∫ ω, Y s ω * Y t ω ∂P) =
        ((s:ℝ)^(2*H)+(t:ℝ)^(2*H)-|(s:ℝ)-(t:ℝ)|^(2*H))/2) ∧
      ∀ᵐ ω ∂P, ∀ α : ℝ, 0 ≤ α → α < H → ∀ N : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ≥0, s ≤ N → t ≤ N →
          dist (Y s ω) (Y t ω) ≤ C * (dist s t)^α := by
  obtain ⟨I, hI⟩ := independent_wiener_actual_integrals P B
  exact ⟨I, hI, Asakura.mandelbrot_van_ness P I H hH0 hH1⟩

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.mandelbrot_van_ness_from_brownian_system
