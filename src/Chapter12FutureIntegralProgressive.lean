import Chapter12ConditionalProgressive
import Chapter12IndependentConditionalIntegral

open MeasureTheory Set ProbabilityTheory
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Integrating an independent copy of the future preserves progressive
measurability. The future is integrated on a fixed probability space, so
there is no time-dependent choice of representatives or Gaussian bases. -/
theorem independent_future_integral_progressive
    {Ω S E G Ξ : Type*} [Preorder S] [MeasurableSpace S]
    [MeasurableSpace E] [MeasurableSpace G] [MeasurableSpace Ξ]
    (F : S → MeasurableSpace Ω) (ν : Measure Ξ) [SigmaFinite ν]
    (X : Ω × S → E) (Y : S × Ξ → G)
    (hX : @Measurable _ _ (progressiveSpace F) inferInstance X)
    (hY : Measurable Y) (f : E × G → ℝ) (hf : Measurable f) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × S => ∫ y,f (X z,Y (z.2,y)) ∂ν) := by
  apply (measurable_progressive_iff _ _).mpr
  intro t
  letI : MeasurableSpace Ω := F t
  have hXt := (measurable_progressive_iff _ _).mp hX t
  have hj : Measurable (fun z : (Ω × Iic t) × Ξ =>
      f (X (z.1.1,z.1.2.val),Y (z.1.2.val,z.2))) := by
    apply hf.comp
    apply Measurable.prodMk
    · exact hXt.comp measurable_fst
    · exact hY.comp ((measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

end Asakura.Chapter12
