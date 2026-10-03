import Chapter3SmoothPositivePower

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1000000

/-- A concrete C² extension of a shifted real power from the nonnegative half-line. -/
theorem shifted_power_extension (a r : ℝ) (ha : 0 < a) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧
      (∀ x, 0 ≤ x → v x = (a+x)^r) ∧
      (∀ x, 0 ≤ x → deriv v x = r*(a+x)^(r-1)) := by
  have hq : 0 < a/4 := by positivity
  let v := fun x => positivePowerExtension (a/4) r (a+x)
  refine ⟨v,(positivePowerExtension_contDiff hq r 2).comp (contDiff_const.add contDiff_id),?_,?_⟩
  · intro x hx
    exact (positivePowerExtension_value_deriv hq (by linarith : 2*(a/4) < a+x) r).1
  · intro x hx
    have hbase := ((positivePowerExtension_contDiff hq r 1).differentiable one_ne_zero).differentiableAt.hasDerivAt (x := a+x)
    have hcomp := hbase.comp x ((hasDerivAt_id x).const_add a)
    have he := (positivePowerExtension_value_deriv hq (by linarith : 2*(a/4) < a+x) r).2
    simpa only [v,Function.comp_def,he,mul_one] using hcomp.deriv

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.shifted_power_extension
