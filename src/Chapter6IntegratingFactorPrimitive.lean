import Chapter6IntegratingFactor

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter6

lemma integrating_factor_primitive (α : ℝ → ℝ) (hα : Continuous α) (t : ℝ) :
    linearIntegratingFactor α t=1+∫ r in 0..t,α r*linearIntegratingFactor α r := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r (_ : r∈uIcc 0 t) => integrating_factor_derivative α hα r)
    ((hα.mul (integrating_factor_continuous α hα)).intervalIntegrable 0 t)
  have hz : linearIntegratingFactor α 0=1 := by simp [linearIntegratingFactor]
  rw [hz] at hi
  linarith

end Asakura.Chapter6
