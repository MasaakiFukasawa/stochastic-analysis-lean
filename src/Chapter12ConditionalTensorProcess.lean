import Chapter12ConditionalTensor
import Chapter12ConditionalTimeProjection

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- A separated L2 function inherits a progressive conditional process from
its random coefficient; the equalities are transferred to the actual L2 classes. -/
theorem conditional_tensor_process {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0<T) [Fact (0≤T)]
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hle : ∀ t,F t≤m)
    (U : Lp ℝ 2 P) (h : Lp ℝ 2 (compactTimeMeasure T hT.le))
    (u : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)))
    (hu : (u : Ω × Icc (0:ℝ) T → ℝ) =ᵐ[P.prod (compactTimeMeasure T hT.le)]
      (fun z => h z.2*U z.1))
    (C : Ω × Icc (0:ℝ) T → ℝ)
    (hC : @Measurable _ _ (progressiveSpace F) inferInstance C)
    (he : ∀ t,(fun w => C (w,t)) =ᵐ[P] P[(U : Ω → ℝ)|F t]) :
    ∃ q : Lp ℝ 2 (P.prod (compactTimeMeasure T hT.le)),
      AEStronglyMeasurable[progressiveSpace F] q (P.prod (compactTimeMeasure T hT.le)) ∧
      ∀ᵐ t ∂compactTimeMeasure T hT.le,(fun w => q (w,t)) =ᵐ[P] P[(fun w => u (w,t))|F t] := by
  let ν := compactTimeMeasure T hT.le
  obtain ⟨hqp,hqi,hcond,_⟩ := conditional_tensor_L2 P ν F hle U
    (Lp.stronglyMeasurable U).measurable (Lp.memLp U) h (Lp.stronglyMeasurable h).measurable
    (Lp.memLp h) C hC he
  refine ⟨hqi.toLp _,hqp.aestronglyMeasurable.congr hqi.coeFn_toLp.symm,?_⟩
  have hus := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.ae hu)
  have hqs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.ae hqi.coeFn_toLp)
  filter_upwards [hus,hqs] with t hut hqt
  change (fun w => u (w,t)) =ᵐ[P] (fun w => h t*U w) at hut
  change (fun w => hqi.toLp _ (w,t)) =ᵐ[P] (fun w => h t*C (w,t)) at hqt
  exact (hqt.trans (hcond t)).trans (condExp_congr_ae (m := F t) hut).symm

end Asakura.Chapter12
