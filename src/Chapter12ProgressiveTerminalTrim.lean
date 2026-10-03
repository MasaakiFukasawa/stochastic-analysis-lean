import Chapter12ProductTrim
import Chapter12AdaptedWienerEmbedding

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.Chapter2Complete
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem product_measurable_le {Ω S : Type*} (mT m : MeasurableSpace Ω)
    (mS : MeasurableSpace S) (hle : mT≤m) : mT.prod mS≤m.prod mS :=
  sup_le_sup (MeasurableSpace.comap_mono hle) le_rfl

theorem product_trim_measure {Ω S : Type*} [m : MeasurableSpace Ω] [mS : MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (mT : MeasurableSpace Ω) (hle : mT≤m)
    (ν : Measure S) [SigmaFinite ν] :
    @Measure.prod Ω S mT mS (P.trim hle) ν =
      (@Measure.prod Ω S m mS P ν).trim (product_measurable_le mT m mS hle) := by
  letI : MeasurableSpace Ω := m
  obtain ⟨hpm,hh⟩ := @MeasurePreserving.prod Ω Ω S m mT mS S mS P (P.trim hle) ν ν
    inferInstance inferInstance id id (@trim_identity_preserving Ω m P mT hle) (MeasurePreserving.id ν)
  obtain ⟨him,hi⟩ := @trim_identity_preserving (Ω × S) (m.prod mS) (@Measure.prod Ω S m mS P ν) (mT.prod mS) (product_measurable_le mT m mS hle)
  have he : Prod.map (id : Ω → Ω) (id : S → S)=id := rfl
  change @Measure.map _ _ (m.prod mS) (mT.prod mS) (Prod.map id id) (P.prod ν) = _ at hh
  rw [he] at hh
  exact hh.symm.trans hi

/-- Restricting to terminal information before taking the progressive
sigma algebra gives exactly the same measure on progressive processes. -/
theorem progressive_terminal_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0≤T) [Fact (0≤T)]
    (mT : MeasurableSpace Ω) (hle : mT≤m)
    (F : Icc (0:ℝ) T → MeasurableSpace Ω) (hF : ∀ t,F t≤mT) :
    letI : MeasurableSpace (Ω × Icc (0:ℝ) T) := progressiveSpace F
    (@Measure.prod Ω (Icc (0:ℝ) T) mT inferInstance (P.trim hle) (compactTimeMeasure T hT)).trim
      (progressive_space_le_product F hF) =
    (@Measure.prod Ω (Icc (0:ℝ) T) m inferInstance P (compactTimeMeasure T hT)).trim
      (progressive_space_le_product F (fun t => (hF t).trans hle)) := by
  letI : MeasurableSpace Ω := m
  rw [product_trim_measure P mT hle,trim_trim]

end Asakura.Chapter12
