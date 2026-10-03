import Chapter11DiscountProduct

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1200000

theorem constant_integrator_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)] (c : ℕ → ℝ) (hc : ∀ n,0≤c n)
    (a : Ω → ℝ) (H : Ω × ℝ → ℝ) :
    VariationIntegralFormula (T := T) P c hc (fun _ => a) H (fun _ _ => 0) := by
  intro n
  refine ⟨fun _ => 0,?_,?_,?_,?_⟩
  · simp [SignedMeasure.totalVariation_zero]
  · exact ae_of_all _ (fun w s t _ => by simp)
  · simp [SignedMeasure.totalVariation_zero]
  · exact ae_of_all _ (fun w t => by simp [signedCumulative,signedIntegralRaw,SignedMeasure.toJordanDecomposition_zero])

end Asakura.Chapter12
#print axioms Asakura.Chapter12.constant_integrator_formula
