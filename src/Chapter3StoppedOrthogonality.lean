import Chapter2SquareIntegrableStop
import FullAuditUnboundedPullout

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- In the proof of prop:qcv, the later square-defect martingale vanishes at
the earlier stopping time. Optional sampling gives zero conditional mean;
the earlier random coefficient need only be L2, not bounded. -/
theorem stopped_zero_martingale_orthogonal
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (Y : ClosedTime T → Ω → ℝ) (hY : ContinuousM2Witness P F Y)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hz : (fun ω => Y (σ ω) ω) =ᵐ[P] 0)
    (A : Ω → ℝ) (hA : Measurable[writtenStoppedSpace m F σ hσ] A)
    (hA2 : MemLp A 2 P) :
    (∫ ω, A ω * Y ⊤ ω ∂P) = 0 := by
  let G := writtenStoppedSpace m F σ hσ
  have hG : G ≤ m := fun _ h => h.1
  have ht : ∀ t : ClosedTime T, MeasurableSet[F t] {ω : Ω | (⊤ : ClosedTime T) ≤ t} := by
    intro t
    by_cases h : (⊤ : ClosedTime T) ≤ t <;> simp [h]
  have hce := continuous_optional_sampling_written P (Fact.out : 0 ≤ T) F hF hle Y
    hY.adapted (fun t => (hY.moment t).integrable (by norm_num))
    (fun ω t => (hY.path ω).continuousAt.continuousWithinAt) hY.martingale
    (fun _ => ⊤) σ ht hσ
  have hzero : P[Y ⊤ | G] =ᵐ[P] 0 := by
    have hh : P[Y ⊤ | G] =ᵐ[P] (fun ω => Y (σ ω) ω) := by
      simpa only [min_top_left] using hce
    exact hh.trans hz
  have hi : Integrable (A * Y ⊤) P := hA2.integrable_mul (hY.moment ⊤)
  have hp := unbounded_pullout_by_restriction P hG A (Y ⊤) hA.stronglyMeasurable hi
    ((hY.moment ⊤).integrable (by norm_num))
  have he : P[A * Y ⊤ | G] =ᵐ[P] 0 := by
    filter_upwards [hp,hzero] with ω hp hz
    simpa only [Pi.mul_apply,hz,Pi.zero_apply,mul_zero] using hp
  have heI := integral_congr_ae he
  rw [integral_condExp hG] at heI
  simpa only [Pi.zero_apply,integral_zero,Pi.mul_apply] using heI

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_zero_martingale_orthogonal
