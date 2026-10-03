import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

noncomputable def cappedExp (ε x : ℝ) := Real.exp x/(1+ε*Real.exp x)
noncomputable def cappedExpDeriv (ε x : ℝ) := Real.exp x/(1+ε*Real.exp x)^2

theorem cappedExp_hasDerivAt (ε : ℝ) (hε : 0 ≤ ε) (x : ℝ) :
    HasDerivAt (cappedExp ε) (cappedExpDeriv ε x) x := by
  have hd : 1+ε*Real.exp x ≠ 0 := ne_of_gt (by positivity)
  convert (Real.hasDerivAt_exp x).div
    ((hasDerivAt_const x (1:ℝ)).add ((Real.hasDerivAt_exp x).const_mul ε)) hd using 1
  · rfl
  · dsimp only [cappedExpDeriv]
    congr 1
    simp only [Pi.add_apply]
    ring

theorem cappedExp_bounds (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    0 ≤ cappedExp ε x ∧ cappedExp ε x ≤ Real.exp x ∧
    0 ≤ cappedExpDeriv ε x ∧ cappedExpDeriv ε x ≤ Real.exp x ∧
    |cappedExpDeriv ε x| ≤ 1/ε := by
  have hx := Real.exp_pos x
  have hd : 1 ≤ 1+ε*Real.exp x := le_add_of_nonneg_right (mul_nonneg hε.le hx.le)
  have hdpos : 0 < 1+ε*Real.exp x := by positivity
  have hd2 : 1 ≤ (1+ε*Real.exp x)^2 := by nlinarith
  dsimp only [cappedExp,cappedExpDeriv]
  refine ⟨by positivity,?_,by positivity,?_,?_⟩
  · exact div_le_self hx.le hd
  · exact div_le_self hx.le hd2
  · rw [abs_of_nonneg (by positivity : 0 ≤ Real.exp x/(1+ε*Real.exp x)^2)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hdpos) hε).mpr
    nlinarith [sq_nonneg (ε*Real.exp x)]

theorem cappedExp_derivative_continuous (ε : ℝ) (hε : 0 ≤ ε) :
    Continuous (cappedExpDeriv ε) := by
  apply Real.continuous_exp.div ((continuous_const.add (continuous_const.mul Real.continuous_exp)).pow 2)
  intro x
  change (1+ε*Real.exp x)^2 ≠ 0
  positivity

theorem cappedExp_approximation (x : ℝ) :
    Tendsto (fun n : ℕ => cappedExp (1/(n+1)) x) atTop (𝓝 (Real.exp x)) ∧
    Tendsto (fun n : ℕ => cappedExpDeriv (1/(n+1)) x) atTop (𝓝 (Real.exp x)) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (Real.exp x))
  constructor
  · simpa [cappedExp,Pi.div_def] using (tendsto_const_nhds (x := Real.exp x)).div h (by norm_num)
  · simpa [cappedExpDeriv,Pi.div_def] using (tendsto_const_nhds (x := Real.exp x)).div (h.pow 2) (by norm_num)

end Asakura.Chapter12
