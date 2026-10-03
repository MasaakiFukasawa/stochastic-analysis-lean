import Chapter12NaturalBrownianTrimInformation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Completion of the natural filtration adds no Lp random variables beyond
almost-everywhere equivalence of functions of the Brownian coordinates. -/
theorem natural_brownian_Lp_information {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ) (hT : 0≤T)
    (p : ℝ≥0∞) (U : Lp ℝ p (P.trim ((naturalBrownianSystem P B hB hm hc).le (realTimeClamp T)))) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w z => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w) inferInstance]
      (U : Ω → ℝ) (P.trim ((naturalBrownianSystem P B hB hm hc).le (realTimeClamp T))) := by
  exact natural_brownian_information_on_trim P B hB hm hc T T hT le_rfl U (Lp.stronglyMeasurable U).measurable

/-- Restricting the finite-horizon coordinate family to an earlier time gives
exactly that earlier Brownian coordinate family. -/
theorem natural_brownian_past_information {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ)
    (a : Icc (0:ℝ) T) (G : Ω → ℝ)
    (hG : Measurable[(naturalBrownianSystem P B hB hm hc).F (realTimeClamp a.val)] G) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w (z : BrownianTimeCoordinates 0 a.val) =>
        brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T
          (z.1,⟨z.2.val,z.2.property.1,z.2.property.2.trans a.property.2⟩) w) inferInstance] G
      (P.trim ((naturalBrownianSystem P B hB hm hc).le (realTimeClamp T))) := by
  exact natural_brownian_information_on_trim P B hB hm hc T a.val a.property.1 a.property.2 G hG

end Asakura.Chapter12
