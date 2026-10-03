import Chapter12LpIsometryLift
import Chapter12BrownianDerivativeRealization

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def timeRealizationIsometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0≤T) :
    Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P →ₗᵢ[ℝ]
      Lp ℝ 2 (P.prod (compactTimeMeasure T hT)) :=
  (l2SectionsEquiv P (compactTimeMeasure T hT)).symm.toLinearIsometry.comp
    (lpIsometryLift P 2 (finiteTimeToCompact T hT))

theorem timeRealization_inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0≤T)
    (U V : Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P) :
    inner ℝ (timeRealization P T hT U) (timeRealization P T hT V)=inner ℝ U V :=
  (timeRealizationIsometry P T hT).inner_map_map U V

end Asakura.Chapter12
