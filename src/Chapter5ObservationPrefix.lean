import Chapter5ObservationNoiseMap

open Set
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete

/-- Extending the stop of the current observations from b to S leaves
all observation coordinates unchanged before b. -/
theorem observation_prefix_consistency
    {Ω : Type*} {T : EReal} [Fact (0≤T)] {d k : ℕ}
    (W : Fin d → ClosedTime T → Ω → ℝ) (index : Fin k → Fin d)
    (active : Fin k → Prop) [DecidablePred active] (τ : Fin k → ℝ)
    (b S r : ℝ) (hbr : r≤b) (hbS : b≤S)
    (hcurrent : ∀ i,active i → τ i=b) (w : Ω) :
    (fun i => W (index i) (min (realTimeClamp (τ i)) (realTimeClamp r)) w)=
      (fun i => W (index i) (min (realTimeClamp (if active i then S else τ i)) (realTimeClamp r)) w) := by
  funext i
  by_cases hi : active i
  · simp only [hi,ite_true,hcurrent i hi]
    rw [min_eq_right (real_time_clamp_mono hbr),min_eq_right (real_time_clamp_mono (hbr.trans hbS))]
  · simp only [hi,ite_false]

end Asakura.Chapter5
