import Chapter7BrownianVectorIndependence
import Chapter7BrownianSecondMoments
import Mathlib.Probability.ConditionalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The conditional mean is obtained from independence of the original
Brownian increment, rather than postulated for its time integral. -/
lemma brownian_product_conditional_mean {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (u v : Fin d → ℝ) :
    P[(fun w => (∑ j,u j*(B.W j (realTimeClamp t) w-B.W j (realTimeClamp s) w))*
      (∑ j,v j*(B.W j (realTimeClamp t) w-B.W j (realTimeClamp s) w)))|B.F (realTimeClamp s)]
      =ᵐ[P] fun _ => (t-s)*(∑ j,u j*v j) := by
  let Z := fun w j => B.W j (realTimeClamp t) w-B.W j (realTimeClamp s) w
  let f := fun z : Fin d → ℝ => (∑ j,u j*z j)*(∑ j,v j*z j)
  have hf : Measurable f :=
    (Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))).mul
      (Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j)))
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro j
    exact (((B.martingale j).adapted P B.F _ (real_time_below t (hs.trans hst) (EReal.coe_lt_top _))).mono (B.le _) le_rfl).sub
      (((B.martingale j).adapted P B.F _ (real_time_below s hs (EReal.coe_lt_top _))).mono (B.le _) le_rfl)
  have hZi : Measurable[MeasurableSpace.comap Z inferInstance] Z := Measurable.of_comap_le le_rfl
  have he := condExp_indep_eq hZ.comap_le (B.le (realTimeClamp s))
    (hf.comp hZi).stronglyMeasurable (brownian_vector_increment_independent P B s t hs hst)
  have hm := (brownian_projection_cross P B s t hs hst u v).2
  simpa only [Function.comp_def,f,Z,hm] using he

end Asakura.Chapter7
