import Chapter2OneSidedStoppedCovariance
import Chapter3ContinuousIntegralConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The identity used before applying Novikov to each partition increment.
The cross covariance is proved by the one-sided stopping theorem. -/
theorem after_stop_self_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (Z C : ClosedTime T → Ω → ℝ) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Z Z C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t}) :
    LocalMProcessWitness P F (fun t w => Z t w-Z (min (σ w) t) w) ∧
    LocalCovarianceWitness P F (fun t w => Z t w-Z (min (σ w) t) w)
      (fun t w => Z t w-Z (min (σ w) t) w) (fun t w => C t w-C (min (σ w) t) w) := by
  let S := fun t w => Z (min (σ w) t) w
  let B := fun t w => C (min (σ w) t) w
  have hS := hZ.stopped P F hF hle σ hσ
  have hB := hC.stopped P F hF hle σ hσ
  have hR : LocalMProcessWitness P F (fun t w => Z t w-S t w) := by
    convert hZ.add P F hF hle (hS.smul P F (-1)) using 1
    funext t w
    ring
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull S Z hS hZ
  have hDB := local_covariance_one_sided_stopping P F hF hle hnull Z Z C D hZ hZ hC σ hσ hD
  have hd := (hC.defect.add P F hF hle (hD.defect.smul P F (-2))).add P F hF hle hB.defect
  have hv := hC.variation.add F (hB.variation.smul F (-1))
  have htargetV : LocalVariationWitness F (fun t w => C t w-B t w) := by
    convert hv using 1
    funext t w
    ring
  have hCc w t (ht : t < ⊤) : ContinuousAt (fun s => C s w) t := by
    have hh := ((hZ.path P F w t ht).mul (hZ.path P F w t ht)).sub (hC.defect.path P F w t ht)
    convert hh using 1
    funext s
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    ring
  have hBc w t (ht : t < ⊤) : ContinuousAt (fun s => B s w) t :=
    (hCc w _ ((min_le_right _ _).trans_lt ht)).comp (continuous_const.min continuous_id).continuousAt
  refine ⟨hR,?_,htargetV⟩
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hd
  · intro t ht
    exact ((hR.adapted P F t ht).mul (hR.adapted P F t ht)).sub
      ((hC.adapted P F hZ hZ t ht).sub (hB.adapted P F hS hS t ht))
  · intro w t ht
    exact ((hR.path P F w t ht).mul (hR.path P F w t ht)).sub ((hCc w t ht).sub (hBc w t ht))
  · filter_upwards [hDB] with w hw
    intro t ht
    change (Z t w*Z t w-C t w)+(-2)*(S t w*Z t w-D t w)+(S t w*S t w-B t w) =
      (Z t w-S t w)*(Z t w-S t w)-(C t w-B t w)
    specialize hw t ht
    change D t w = B t w at hw
    rw [hw]
    ring

end Asakura.Chapter6
