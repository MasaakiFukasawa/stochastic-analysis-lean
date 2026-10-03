import Chapter3StoppedIncrementCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Different past observation times may be stopped independently. Their
literal covariance is the original covariance stopped at the earlier time. -/
theorem different_stopped_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n,c n<⊤)
    (hcc : ∀ t,t<⊤ → ∃ n,t<c n)
    (a b : ClosedTime T) (ha : a<⊤) (hb : b<⊤) :
    LocalCovarianceWitness P F (fun t w => X (min a t) w) (fun t w => Y (min b t) w)
      (fun t w => C (min (min a b) t) w) := by
  have hstop (s : ClosedTime T) : ∀ t,MeasurableSet[F t] {w : Ω | s≤t} := by
    intro t
    by_cases h : s≤t <;> simp [h]
  have hXs := hX.stopped P F hF hle (fun _ => a) (hstop a)
  have h1 := actual_one_sided_stopped_covariance P F hF hle hnull X Y C hX hY hC
    c hcm hct hcc (fun _ => a) (hstop a) (fun _ => ha)
  have h2 := actual_one_sided_stopped_covariance P F hF hle hnull Y (fun t w => X (min a t) w)
    (fun t w => C (min a t) w) hY hXs (h1.symm P F)
    c hcm hct hcc (fun _ => b) (hstop b) (fun _ => hb)
  simpa only [min_assoc] using h2.symm P F

end Asakura.Chapter5
