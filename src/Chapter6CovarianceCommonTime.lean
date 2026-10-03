import Chapter5BracketCommonTime
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 1800000

/-- The density formula for actual cross covariances holds simultaneously
at all times of each finite prefix. -/
theorem covariance_density_common_time
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω)
    (X Y C : HalfClosedTime → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (G : Ω × ℝ → ℝ)
    (hi : ∀ b : ℝ,0 ≤ b → ∀ᵐ w ∂P,IntervalIntegrable (fun r => G (w,r)) volume 0 b)
    (he : ∀ r : ℝ,0 ≤ r → C (realTimeClamp r) =ᵐ[P] fun w => ∫ s in 0..r,G (w,s)) :
    ∀ b : ℝ,0 ≤ b → ∀ᵐ w ∂P,∀ r ∈ Icc 0 b,C (realTimeClamp r) w = ∫ s in 0..r,G (w,s) := by
  intro b hb
  apply bracket_primitive_common_time P b hb _ _ _ (hi b hb) (fun r hr => he r hr.1)
  intro w r hr
  exact ((local_covariance_path_continuous P F X Y C hX hY hC w _ (changed_time_finite r hr.1)).comp
    real_time_clamp_continuous.continuousAt).continuousWithinAt

end Asakura.Chapter6
