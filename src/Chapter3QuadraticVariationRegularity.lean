import Chapter3ContinuousAdaptedWeights

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Covariance continuity follows from XY-C being a local martingale. -/
theorem covariance_continuous_at
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (ω : Ω) (t : ClosedTime T) (ht : t < ⊤) :
    ContinuousAt (fun s => C s ω) t := by
  have h := ((hX.path P F ω t ht).mul (hY.path P F ω t ht)).sub (hC.defect.path P F ω t ht)
  convert h using 1
  funext s
  simp only [Pi.sub_apply,Pi.mul_apply,sub_sub_cancel]

/-- The finite-interval regularity required by the actual Stieltjes
measure is derived directly from the covariance witness. -/
theorem covariance_real_continuous_on
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (d : ℝ) (hdT : (d:EReal) < T) (ω : Ω) :
    ContinuousOn (fun r => C (realTimeClamp r) ω) (Icc 0 d) := by
  intro r hr
  have hrt : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hdT
  exact ((covariance_continuous_at P F X Y C hX hY hC ω _ hrt).comp
    real_time_clamp_continuous.continuousAt).continuousWithinAt

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.covariance_continuous_at
#print axioms Asakura.Chapter3Complete.covariance_real_continuous_on
