import Chapter6IncrementCovariance
import Chapter3OpenProcessRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- A stopped local martingale followed by the increments of another
has the sum of the two disjoint-time quadratic variations. The cross
term is proved local by one-sided stopping, not set equal to zero by
an assumption about independence. -/
theorem concatenated_local_covariance
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t E,MeasurableSet E → P E = 0 → MeasurableSet[F t] E)
    (X Y C D : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X X C) (hD : LocalCovarianceWitness P F Y Y D)
    (σ : Ω → ClosedTime T) (hσ : ∀ t,MeasurableSet[F t] {w | σ w ≤ t}) :
    let Z := fun t w => X (min (σ w) t) w+(Y t w-Y (min (σ w) t) w)
    let A := fun t w => C (min (σ w) t) w+(D t w-D (min (σ w) t) w)
    LocalMProcessWitness P F Z ∧ LocalCovarianceWitness P F Z Z A := by
  let U := fun t w => X (min (σ w) t) w
  let V := fun t w => Y t w-Y (min (σ w) t) w
  let Cs := fun t w => C (min (σ w) t) w
  let Dr := fun t w => D t w-D (min (σ w) t) w
  have hU := hX.stopped P F hF hle σ hσ
  have hCs := hC.stopped P F hF hle σ hσ
  obtain ⟨hV,hDr⟩ := Asakura.Chapter6.after_stop_self_covariance P F hF hle hnull Y D hY hD σ hσ
  obtain ⟨K,hK⟩ := local_covariance_witness_exists P F hF hle hnull X Y hX hY
  obtain ⟨L,hL⟩ := local_covariance_witness_exists P F hF hle hnull U Y hU hY
  have he := local_covariance_one_sided_stopping P F hF hle hnull X Y K L hX hY hK σ hσ hL
  have hKs := hK.stopped P F hF hle σ hσ
  have hp := hL.defect.add P F hF hle (hKs.defect.smul P F (-1))
  have hUV : LocalMProcessWitness P F (fun t w => U t w*V t w) := by
    apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hp
    · intro t ht
      exact (hU.adapted P F t ht).mul (hV.adapted P F t ht)
    · intro w t ht
      exact (hU.path P F w t ht).mul (hV.path P F w t ht)
    · filter_upwards [he] with w hw
      intro t ht
      change (U t w*Y t w-L t w)+(-1)*(U t w*Y (min (σ w) t) w-K (min (σ w) t) w) =
        U t w*(Y t w-Y (min (σ w) t) w)
      rw [hw t ht]
      ring
  have hZ := hU.add P F hF hle hV
  have hdef := (hCs.defect.add P F hF hle hDr.defect).add P F hF hle (hUV.smul P F 2)
  refine ⟨hZ,?_,hCs.variation.add F hDr.variation⟩
  convert hdef using 1
  funext t w
  change (U t w+V t w)*(U t w+V t w)-(Cs t w+Dr t w) =
    (U t w*U t w-Cs t w)+(V t w*V t w-Dr t w)+2*(U t w*V t w)
  ring

end Asakura.Chapter7
