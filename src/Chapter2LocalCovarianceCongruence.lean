import Chapter2LocalPathEncoding
import Chapter2LocalCovarianceRules

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter2Written
set_option maxHeartbeats 700000

/-- Covariation also ignores the dummy terminal values in the half-open
process encoding. Only equality strictly before T is required. -/
theorem LocalCovarianceWitness.congr_processes_before_terminal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X Y X' Y' C : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Y C)
    (hX : ∀ t, t < ⊤ → X t = X' t) (hY : ∀ t, t < ⊤ → Y t = Y' t) :
    LocalCovarianceWitness P F X' Y' C := by
  refine ⟨hC.defect.congr_before_terminal P F ?_,hC.variation⟩
  intro t ht
  funext ω
  rw [congrFun (hX t ht) ω,congrFun (hY t ht) ω]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.congr_processes_before_terminal
