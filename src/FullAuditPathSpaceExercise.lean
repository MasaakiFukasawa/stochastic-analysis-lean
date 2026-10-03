import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Instances.NNReal.Lemmas

open MeasureTheory
open scoped NNReal
namespace Asakura.FullAudit

/-- The path variable takes values in the actual compact-open function space on
 the entire half-line. The Borel criterion is proved in Mathlib by countably
 many evaluations and compact exhaustion, as suggested in the exercise. -/
theorem continuous_adapted_path_measurable {Ω E : Type*} {m : MeasurableSpace Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : ℝ≥0 → MeasurableSpace Ω) (hF : ∀ t, F t ≤ m)
    (Y : ℝ≥0 → Ω → E) (hY : ∀ t, Measurable[F t] (Y t))
    (hc : ∀ ω, Continuous (fun t => Y t ω)) :
    Measurable[m] (fun ω => (⟨fun t => Y t ω,hc ω⟩ : C(ℝ≥0,E))) := by
  exact ContinuousMap.measurable_iff_eval.mpr (fun t => (hY t).mono (hF t) le_rfl)

end Asakura.FullAudit
