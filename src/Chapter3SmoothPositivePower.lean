import Chapter3VariationChainRule
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
set_option maxHeartbeats 1600000

/-- A positive smooth replacement for the identity, equal to it above 2a.
This supplies the extension mentioned in the p<2 BDG argument. -/
noncomputable def smoothPositive (a x : ℝ) : ℝ :=
  a+Real.smoothTransition ((x-a)/a)*(x-a)

theorem smoothPositive_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < smoothPositive a x := by
  by_cases hx : x ≤ a
  · have ht : (x-a)/a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) ha.le
    simp only [smoothPositive,Real.smoothTransition.zero_of_nonpos ht,zero_mul,add_zero]
    exact ha
  · have h := mul_nonneg (Real.smoothTransition.nonneg ((x-a)/a)) (sub_nonneg.mpr (le_of_not_ge hx))
    dsimp [smoothPositive]
    linarith

theorem smoothPositive_eq {a x : ℝ} (ha : 0 < a) (hx : 2*a ≤ x) : smoothPositive a x = x := by
  have ht : 1 ≤ (x-a)/a := (le_div_iff₀ ha).mpr (by linarith)
  simp only [smoothPositive,Real.smoothTransition.one_of_one_le ht,one_mul]
  ring

theorem smoothPositive_contDiff (a : ℝ) (n : ℕ) : ContDiff ℝ n (smoothPositive a) := by
  exact contDiff_const.add ((Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const a)).mul (contDiff_id.sub contDiff_const))

noncomputable def positivePowerExtension (a r x : ℝ) : ℝ := (smoothPositive a x)^r

theorem positivePowerExtension_contDiff {a : ℝ} (ha : 0 < a) (r : ℝ) (n : ℕ) :
    ContDiff ℝ n (positivePowerExtension a r) := by
  exact (smoothPositive_contDiff a n).rpow contDiff_const (fun x => (smoothPositive_pos ha x).ne')

theorem positivePowerExtension_value_deriv {a x : ℝ} (ha : 0 < a) (hx : 2*a < x) (r : ℝ) :
    positivePowerExtension a r x = x^r ∧ deriv (positivePowerExtension a r) x = r*x^(r-1) := by
  have he : positivePowerExtension a r =ᶠ[𝓝 x] (fun y => y^r) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact congrArg (fun z : ℝ => z^r) (smoothPositive_eq ha hy.le)
  refine ⟨he.eq_of_nhds,?_⟩
  rw [he.deriv_eq]
  exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith : x ≠ 0))).deriv

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.smoothPositive_pos
#print axioms Asakura.Chapter3Complete.smoothPositive_eq
#print axioms Asakura.Chapter3Complete.smoothPositive_contDiff
#print axioms Asakura.Chapter3Complete.positivePowerExtension_contDiff
#print axioms Asakura.Chapter3Complete.positivePowerExtension_value_deriv
