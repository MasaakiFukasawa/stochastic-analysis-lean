import Chapter12ProductTrim
import Chapter12CompactTimeMeasure

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Increment tests pass to terminal information without changing either
expectation. All measurability requirements are explicit. -/
theorem terminal_step_pairing {Ω S : Type*} [m : MeasurableSpace Ω]
    [mS : MeasurableSpace S] (P : Measure Ω) [IsProbabilityMeasure P]
    (mT : MeasurableSpace Ω) (hle : mT ≤ m) (ν : Measure S) [SigmaFinite ν]
    (H : Ω × S → ℝ) (hH : @Measurable _ _ (mT.prod mS) inferInstance H)
    (G Y Z : Ω → ℝ) (hG : Measurable[mT] G) (hY : Measurable[mT] Y)
    (hZ : Measurable[mT] Z) (A : Set S) (hA : MeasurableSet A)
    (hpair : (@integral (Ω × S) ℝ _ _ (m.prod mS) (@Measure.prod Ω S m mS P ν)
      (fun z => H z*A.indicator (fun _ => G z.1) z.2)) =
      ∫ w,Y w*G w*Z w ∂P) :
    (@integral (Ω × S) ℝ _ _ (mT.prod mS) (@Measure.prod Ω S mT mS (P.trim hle) ν)
      (fun z => H z*A.indicator (fun _ => G z.1) z.2)) =
    (@integral Ω ℝ _ _ mT (P.trim hle) (fun w => Y w*G w*Z w)) := by
  have hm : @Measurable _ _ (mT.prod mS) inferInstance
      (fun z : Ω × S => H z*A.indicator (fun _ => G z.1) z.2) :=
    hH.mul ((hG.comp measurable_fst).indicator (hA.preimage measurable_snd))
  rw [@product_trim_integral Ω S m mS P inferInstance mT hle ν inferInstance _ hm,hpair]
  exact integral_trim hle ((hY.mul hG).mul hZ).stronglyMeasurable

end Asakura.Chapter12
