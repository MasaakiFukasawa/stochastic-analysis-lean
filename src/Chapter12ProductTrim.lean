import Chapter12ProbabilityTrim
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem trim_identity_preserving {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (mT : MeasurableSpace Ω) (hle : mT ≤ m) :
    @MeasurePreserving Ω Ω m mT id P (P.trim hle) := by
  have hi : @Measurable Ω Ω m mT id := measurable_id.mono le_rfl hle
  apply @MeasurePreserving.mk Ω Ω m mT id P (P.trim hle) hi
  apply Measure.ext
  intro s hs
  rw [@Measure.map_apply Ω Ω m mT P id hi s hs,trim_measurableSet_eq hle hs]
  rfl

theorem product_trim_memLp {Ω S E : Type*} [m : MeasurableSpace Ω] [mS : MeasurableSpace S]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (ν : Measure S) [SigmaFinite ν] (f : Ω × S → E)
    (hf : @Measurable _ _ (mT.prod mS) inferInstance f) (p : ℝ≥0∞) :
    @MemLp _ _ (mT.prod mS) _ _ f p (@Measure.prod Ω S mT mS (P.trim hle) ν) ↔
      @MemLp _ _ (m.prod mS) _ _ f p (@Measure.prod Ω S m mS P ν) := by
  obtain ⟨hm,he⟩ := @MeasurePreserving.prod Ω Ω S m mT mS S mS P (P.trim hle) ν ν
    inferInstance inferInstance id id (@trim_identity_preserving Ω m P mT hle) (MeasurePreserving.id ν)
  have hh := @memLp_map_measure_iff (Ω × S) (m.prod mS) p (@Measure.prod Ω S m mS P ν)
    E _ _ (Ω × S) (mT.prod mS) (Prod.map id id) f hf.aestronglyMeasurable hm.aemeasurable
  rw [he] at hh
  simpa only [Function.comp_def,Prod.map_def,id_eq] using hh

theorem product_trim_integral {Ω S : Type*} [m : MeasurableSpace Ω] [mS : MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (mT : MeasurableSpace Ω) (hle : mT ≤ m)
    (ν : Measure S) [SigmaFinite ν] (f : Ω × S → ℝ)
    (hf : @Measurable _ _ (mT.prod mS) inferInstance f) :
    (@integral (Ω × S) ℝ _ _ (mT.prod mS) (@Measure.prod Ω S mT mS (P.trim hle) ν) f) =
      @integral (Ω × S) ℝ _ _ (m.prod mS) (@Measure.prod Ω S m mS P ν) f := by
  obtain ⟨hm,he⟩ := @MeasurePreserving.prod Ω Ω S m mT mS S mS P (P.trim hle) ν ν
    inferInstance inferInstance id id (@trim_identity_preserving Ω m P mT hle) (MeasurePreserving.id ν)
  have hh := @integral_map (Ω × S) ℝ _ _ (m.prod mS) (@Measure.prod Ω S m mS P ν)
    (Ω × S) (mT.prod mS) (Prod.map id id) hm.aemeasurable f hf.aestronglyMeasurable
  rw [he] at hh
  simpa only [Prod.map_def,id_eq] using hh

end Asakura.Chapter12
