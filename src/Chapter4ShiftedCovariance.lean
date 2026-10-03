import Chapter4DeterministicTimeShift
import Chapter4UnboundedInitialWeight

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Covariation shifts by subtracting its value at the restart time.
The two random initial-value cross terms are actual local martingales. -/
theorem covariance_shifted_future
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X Y C : HalfClosedTime → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C) (s : ℝ) (hs : 0≤s) :
    let φ := deterministicTimeShift s hs
    LocalCovarianceWitness P (fun t => F (φ t))
      (fun t w => X (φ t) w-X (φ ⊥) w) (fun t w => Y (φ t) w-Y (φ ⊥) w)
      (fun t w => C (φ t) w-C (φ ⊥) w) := by
  dsimp only
  let φ := deterministicTimeShift s hs
  let G := fun t => F (φ t)
  have hGt : Monotone G := hF.comp (deterministic_shift_mono s hs)
  have hGl t : G t≤m := hle (φ t)
  have hGn t E (hm : MeasurableSet[m] E) (hz : P E=0) : MeasurableSet[G t] E := hnull (φ t) E hm hz
  have htop : (0:EReal)<⊤ := EReal.coe_lt_top 0
  have hzero : (⊥:HalfClosedTime)<⊤ := htop
  have hφ0 : φ ⊥<⊤ := deterministic_shift_below_top s hs ⊥ hzero
  have hx := local_martingale_shifted_future P F hF hle X hX s hs
  have hy := local_martingale_shifted_future P F hF hle Y hY s hs
  have hc := local_martingale_shifted_future P F hF hle _ hC.defect s hs
  have hxy := unbounded_initial_weight_local P htop G hGt hGl hGn _ hy (X (φ ⊥)) (hX.adapted P F _ hφ0)
  have hyx := unbounded_initial_weight_local P htop G hGt hGl hGn _ hx (Y (φ ⊥)) (hY.adapted P F _ hφ0)
  refine ⟨?_,local_variation_time_change_increment F φ (deterministicTimeUnshift s)
    (deterministic_shift_mono s hs) (deterministic_unshift_mono s)
    (deterministic_shift_adjunction s hs) (deterministic_shift_section s hs)
    (deterministic_shift_below_top s hs) (deterministic_unshift_below_top s) C hC.variation⟩
  have hh := (hc.add P G hGt hGl (hxy.smul P G (-1))).add P G hGt hGl (hyx.smul P G (-1))
  convert hh using 1
  funext t w
  dsimp only [φ,G]
  ring

end Asakura.Chapter4
