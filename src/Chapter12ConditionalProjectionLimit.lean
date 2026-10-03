import Chapter12ConditionalTimeClosed
import Chapter12ConditionalTimeProjection

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The approximation argument in Clark--Ocone: construct conditional
processes for the approximants, then pass to the joint L2 limit using the
continuous orthogonal projection and the closed timewise identity. -/
theorem conditional_projection_of_approximants {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet N → P N=0 → MeasurableSet[F t] N)
    (u : ℕ → Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)))
    (U : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)))
    (hu : Tendsto u atTop (𝓝 U))
    (hex : ∀ n,∃ q : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)),
      AEStronglyMeasurable[progressiveSpace F] q (P.prod (compactTimeMeasure T hT.le)) ∧
      ∀ᵐ t ∂compactTimeMeasure T hT.le,
        (fun w => q (w,t)) =ᵐ[P] P[(fun w => u n (w,t))|F t]) :
    let Q : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)) :=
      condExpL2 ℝ ℝ (progressive_space_le_product F hle) U
    ∀ᵐ t ∂compactTimeMeasure T hT.le,(fun w => Q (w,t)) =ᵐ[P] P[(fun w => U (w,t))|F t] := by
  classical
  choose q hqp hqc using hex
  let A := lpMeas ℝ ℝ (progressiveSpace F) 2 (P.prod (compactTimeMeasure T hT.le))
  let L := A.subtypeL.comp (condExpL2 ℝ ℝ (progressive_space_le_product F hle))
  have he n : q n=L (u n) := conditional_time_projection P T hT F hF hle hnull
    (u n) (q n) (hqp n) (hqc n)
  have hq : Tendsto q atTop (𝓝 (L U)) := by
    have hh := L.continuous.continuousAt.tendsto.comp hu
    simpa only [Function.comp_def,← he] using hh
  exact conditional_time_identity_closed P (compactTimeMeasure T hT.le) F hle u q U (L U) hu hq hqc

end Asakura.Chapter12
