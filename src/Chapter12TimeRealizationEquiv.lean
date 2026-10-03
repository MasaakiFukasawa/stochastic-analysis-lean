import Chapter12LpIsometryEquivLift
import Chapter12CompactTimeInverse
import Chapter12TimeRealizationIsometry

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def finiteCompactTimeEquiv (T : ℝ) (hT : 0≤T) :
    Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (compactTimeMeasure T hT) :=
  LinearIsometryEquiv.ofSurjective (finiteTimeToCompact T hT)
    (fun f => ⟨compactTimeToFinite T hT f,compact_finite_time_inverse T hT f⟩)

noncomputable def timeRealizationEquiv {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0≤T) :
    Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P ≃ₗᵢ[ℝ]
      Lp ℝ 2 (P.prod (compactTimeMeasure T hT)) :=
  (lpIsometryEquivLift P 2 (finiteCompactTimeEquiv T hT)).trans
    (l2SectionsEquiv P (compactTimeMeasure T hT)).symm

theorem timeRealizationEquiv_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ) (hT : 0≤T)
    (U : Lp (Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) 2 P) :
    timeRealizationEquiv P T hT U=timeRealization P T hT U := rfl

end Asakura.Chapter12
