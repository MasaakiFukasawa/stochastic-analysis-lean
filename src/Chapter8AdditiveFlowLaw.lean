import FullAuditTransportFlow
import Chapter8OUStationary

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- The transition law of a measurable additive random flow is the
convolution of its deterministic image with the actual noise law. -/
theorem additive_flow_law {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure E) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : E → E) (hA : Measurable A) (Z : Ω → E) (hZ : Measurable Z) :
    flowLaw μ P (fun x w => A x+Z w)=(μ.map A) ∗ (P.map Z) := by
  rw [Measure.conv,Measure.map_prod_map μ P hA hZ,
    Measure.map_map (by fun_prop) (hA.prodMap hZ)]
  rfl

end Asakura.Chapter8
