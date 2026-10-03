import Chapter3BDGTwoMoments

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Running maximum commutes with stopping, including the common-time norm representation. -/
theorem runningMaximum_stopped
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t)
    (σ : Ω → ClosedTime T)
    (hcs : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X (min (σ ω) s) ω) t)
    (b : ClosedTime T) (hb : b < ⊤) (ω : Ω) :
    runningMaximum (fun t ω => X (min (σ ω) t) ω) hcs b ω =
      runningMaximum X hc (min (σ ω) b) ω := by
  rw [runningMaximum_of_lt_top _ hcs b hb ω,
    runningMaximum_of_lt_top X hc _ ((min_le_right (σ ω) b).trans_lt hb) ω]
  congr 1
  ext s
  change X (min (σ ω) (min b s)) ω = X (min (min (σ ω) b) s) ω
  rw [min_assoc]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.runningMaximum_stopped
