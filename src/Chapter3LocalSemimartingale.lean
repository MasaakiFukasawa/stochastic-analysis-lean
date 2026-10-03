import Chapter3IncreasingAdaptedVariation
import Chapter2SemimartingaleDecomposition

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

theorem local_martingale_semimartingale_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X) :
    SemimartingaleDecomposition P F X (fun _ _ => 0) X := by
  refine ⟨continuous_increasing_adapted_variation hT F hF _
    (fun _ _ => measurable_const) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ _ _ => continuousAt_const),hX,hX.path P F,?_⟩
  intro t ht ω
  simp

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.local_martingale_semimartingale_decomposition
