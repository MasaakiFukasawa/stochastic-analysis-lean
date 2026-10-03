import Chapter3StoppedMartingaleFromLp
import Chapter8BrownianForcingPath

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- An integrable common bound on a finite interval turns a local martingale
into a true stopped martingale; no fourth moment is needed for products. -/
theorem finite_l2_dominated_local_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (Z : HalfClosedTime → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (b : ℝ) (hb : 0≤b) (D : Ω → ℝ) (hD : MemLp D 2 P)
    (hbound : ∀ᵐ w ∂P,∀ t,‖Z (min (realTimeClamp b) t) w‖≤D w) :
    ContinuousMpWitness P F 2 (fun t w => Z (min (realTimeClamp b) t) w) := by
  let τ := fun _ : Ω => realTimeClamp (T := ⊤) b
  have hs : ∀ t,MeasurableSet[F t] {w : Ω | τ w≤t} := by
    intro t
    by_cases h : realTimeClamp (T := ⊤) b≤t <;> simp [τ,h]
  have ht : ∀ w,τ w<⊤ := fun _ => half_real_time_finite b
  obtain ⟨ha,hc⟩ := hZ.stopped_regular P F hF hle τ hs ht
  let Y := continuousPath (fun t w => Z (min (τ w) t) w) hc
  have hm : Measurable Y := continuous_path_measurable _ hc (fun t => (ha t).mono (hle t) le_rfl)
  have hi : MemLp Y 2 P := by
    apply hD.of_le hm.aestronglyMeasurable
    filter_upwards [hbound] with w hw
    have hd : 0≤D w := (norm_nonneg _).trans (hw ⊥)
    rw [Real.norm_eq_abs,abs_of_nonneg hd]
    exact (ContinuousMap.norm_le _ hd).mpr hw
  have hh := stopped_martingale_of_path_memLp P F hF hle Z hZ τ hs ht 2 (by norm_num) hc
    (by simpa only [ENNReal.ofReal_ofNat] using hi)
  simpa only [ENNReal.ofReal_ofNat] using hh

end Asakura.Chapter10
