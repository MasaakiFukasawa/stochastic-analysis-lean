import Chapter12NaturalBrownianLpInformation
import Chapter12BrownianCompactPath

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem natural_brownian_path_Lp_information {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ) (hT : 0≤T)
    (p : ℝ≥0∞) (U : Lp ℝ p (P.trim ((naturalBrownianSystem P B hB hm hc).le (realTimeClamp T)))) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fun w t => brownianCompactPath B hc T w t) inferInstance]
      (U : Ω → ℝ) (P.trim ((naturalBrownianSystem P B hB hm hc).le (realTimeClamp T))) := by
  have hu := natural_brownian_Lp_information P B hB hm hc T hT p U
  apply hu.mono
  let X := fun w t => brownianCompactPath B hc T w t
  have hmX : Measurable (fun f : Icc (0:ℝ) T → ℝ => fun z : BrownianTimeCoordinates 0 T => f z.2) :=
    Measurable.of_eval (fun z => measurable_pi_apply z.2)
  have he : (fun w z => brownianTimeCoordinate P (naturalBrownianSystem P B hB hm hc) T z w)=
      (fun f : Icc (0:ℝ) T → ℝ => fun z : BrownianTimeCoordinates 0 T => f z.2) ∘ X := by
    funext w z
    exact natural_brownian_coordinate P B hB hm hc T z w
  exact MeasurableSpace.comap_le_comap_of_eq_comp _ hmX he

end Asakura.Chapter12
