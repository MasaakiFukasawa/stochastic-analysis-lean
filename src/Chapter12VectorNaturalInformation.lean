import Chapter12NaturalBrownianTrimInformation

open MeasureTheory Set
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem vector_natural_information_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P (d+1))
    (T a : ℝ) (haT : a≤T)
    (hnat : B.F (realTimeClamp a)=Asakura.nullAugmentation (m:=m) P
      (MeasurableSpace.comap (fun w z => brownianTimeCoordinate P B a z w) inferInstance))
    (f : Ω → ℝ) (hf : Measurable[B.F (realTimeClamp a)] f) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w z => brownianTimeCoordinate P B a z w) inferInstance] f (P.trim (B.le (realTimeClamp T))) := by
  have hcoord_each := brownian_time_coordinate_measurable P B a
  have hcoords : Measurable[B.F (realTimeClamp a)] (fun w z => brownianTimeCoordinate P B a z w) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp a)
    exact Measurable.of_eval hcoord_each
  have ha : MeasurableSpace.comap (fun w z => brownianTimeCoordinate P B a z w) inferInstance≤m :=
    hcoords.comap_le.trans (B.le _)
  have he := null_augmentation_aestronglyMeasurable P _ ha f (hnat ▸ hf)
  exact aestronglyMeasurable_on_terminal_space P (B.F (realTimeClamp T)) _ (B.le _)
    (hcoords.comap_le.trans (B.mono (real_time_clamp_mono haT))) f
    (hf.mono (B.mono (real_time_clamp_mono haT)) le_rfl) he
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_natural_information_on_trim
