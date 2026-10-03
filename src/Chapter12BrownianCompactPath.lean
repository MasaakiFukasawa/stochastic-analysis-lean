import Chapter12NaturalBrownianInformation
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

noncomputable def brownianCompactPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ) : Ω → C(Icc (0:ℝ) T,ℝ) :=
  fun w => ⟨fun t => B ⟨t.val,t.property.1⟩ w,
    (hc w).comp (continuous_subtype_val.subtype_mk (fun t : Icc (0:ℝ) T => t.property.1))⟩

theorem brownian_compact_path_terminal_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hc : ∀ w,Continuous (fun t => B t w)) (T : ℝ) :
    Measurable[(naturalBrownianSystem P B hB hm hc).F (realTimeClamp T)] (brownianCompactPath B hc T) := by
  let BS := naturalBrownianSystem P B hB hm hc
  have hcoords := brownian_time_coordinate_measurable P BS T
  have he (t : Icc (0:ℝ) T) : (fun w => brownianTimeCoordinate P BS T (0,t) w) = fun w => brownianCompactPath B hc T w t := by
    funext w
    exact natural_brownian_coordinate P B hB hm hc T (0,t) w
  letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hh := hcoords (0,t)
  exact (he t) ▸ hh

end Asakura.Chapter12
