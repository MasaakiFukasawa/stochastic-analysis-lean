import Chapter12NaturalBrownianInformation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem aestronglyMeasurable_on_terminal_space {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (mT G : MeasurableSpace Ω) (hT : mT≤m) (hG : G≤mT)
    (f : Ω → ℝ) (hfm : Measurable[mT] f) (hf : AEStronglyMeasurable[G] f P) :
    AEStronglyMeasurable[G] f (P.trim hT) := by
  obtain ⟨g,hgm,hfg⟩ := hf
  exact ⟨g,hgm,hfm.stronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hT (hgm.mono hG) hfg⟩

/-- The completed natural filtration supplies the natural-information
hypotheses of the finite Brownian Malliavin construction and of Clark--Ocone. -/
theorem natural_brownian_information_on_trim {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w))
    (T a : ℝ) (ha : 0≤a) (haT : a≤T) (f : Ω → ℝ)
    (hf : Measurable[(naturalBrownianSystem P B hB hm hc).F (realTimeClamp a)] f) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w z => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) a z w) inferInstance] f
      (P.trim ((naturalBrownianSystem P B hB hm hc).le (realTimeClamp T))) := by
  let BS := naturalBrownianSystem P B hB hm hc
  have hcoords := brownian_time_coordinate_measurable P BS a
  have hcoord : Measurable[BS.F (realTimeClamp T)]
      (fun w z => brownianTimeCoordinate P BS a z w) := by
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    apply Measurable.of_eval
    intro z
    exact (hcoords z).mono
      (BS.mono (real_time_clamp_mono haT)) le_rfl
  apply aestronglyMeasurable_on_terminal_space P (BS.F (realTimeClamp T)) _ (BS.le _)
    hcoord.comap_le f (hf.mono (BS.mono (real_time_clamp_mono haT)) le_rfl)
  exact natural_brownian_measurable_information P B hB hm hc a ha f hf

end Asakura.Chapter12
