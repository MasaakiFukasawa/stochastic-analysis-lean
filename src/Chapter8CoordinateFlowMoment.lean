import Chapter8FlowSecondMoment
import Chapter8InvariantCoordinateConvergence

open MeasureTheory
namespace Asakura.Chapter8
open Asakura.FullAudit
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- A contraction after a fixed invertible linear change of coordinates
preserves finite second moments. -/
theorem coordinate_flow_second_moment {E G Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace Ω]
    (A : E ≃L[ℝ] G) (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ : MemLp (fun x : E => x) 2 μ)
    (F : E → Ω → E) (hF : Measurable (Function.uncurry F)) (h0 : MemLp (F 0) 2 P)
    (a : ℝ) (ha : 0≤a)
    (hc : ∀ x y,∀ᵐ w ∂P,‖A (F x w)-A (F y w)‖≤a*‖A x-A y‖) :
    MemLp (fun x : E => x) 2 (flowLaw μ P F) := by
  apply flow_second_moment μ P F hF hμ h0 (‖A.symm.toContinuousLinearMap‖*a*‖A.toContinuousLinearMap‖)
  intro x
  filter_upwards [hc x 0] with w hw
  simp only [map_zero,sub_zero] at hw
  calc
    ‖F x w-F 0 w‖ = ‖A.symm (A (F x w)-A (F 0 w))‖ := by rw [←map_sub,A.symm_apply_apply]
    _ ≤ ‖A.symm.toContinuousLinearMap‖*‖A (F x w)-A (F 0 w)‖ := A.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖A.symm.toContinuousLinearMap‖*(a*‖A x‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ ≤ ‖A.symm.toContinuousLinearMap‖*(a*(‖A.toContinuousLinearMap‖*‖x‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (A.toContinuousLinearMap.le_opNorm x) ha) (norm_nonneg _)
    _ = _ := by ring

end Asakura.Chapter8
