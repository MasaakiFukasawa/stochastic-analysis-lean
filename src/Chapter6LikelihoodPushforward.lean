import Chapter6PositiveRealDensity
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter6
set_option maxHeartbeats 1800000

/-- If the likelihood is a measurable function of the observed path, its
pushforward has that same density. This is the change-of-variables step
in the statistical model, rather than an assumed RN identity. -/
theorem likelihood_pushforward
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → E) (hX : Measurable X)
    (L : E → ℝ≥0∞) (hL : Measurable L) :
    (P.withDensity (fun w => L (X w))).map X = (P.map X).withDensity L := by
  ext A hA
  rw [Measure.map_apply hX hA,withDensity_apply _ (hX hA),withDensity_apply _ hA]
  rw [Measure.restrict_map hX hA]
  exact (lintegral_map hL hX).symm

/-- Equivalent models cannot assign probability one to distinct values of
a single estimator. This verifies the manuscript's identifiability remark. -/
theorem equivalent_models_no_exact_estimator
    {Ω Θ : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure Q]
    (hPQ : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (T : Ω → Θ) (a b : Θ) (ha : T =ᵐ[P] fun _ => a) (hb : T =ᵐ[Q] fun _ => b) : a = b := by
  obtain ⟨w,hw⟩ := ((hPQ _).mp ha).and hb |>.exists
  exact hw.1.symm.trans hw.2

end Asakura.Chapter6
