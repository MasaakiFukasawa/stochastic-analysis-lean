import Chapter12FiniteDerivativeGrowthProduct
import Chapter12LinearCylinder
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open scoped ContDiff
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000

noncomputable def reciprocalSquareRegularizer (ε x : ℝ) : ℝ := (x^2+ε)⁻¹

theorem reciprocal_square_regularizer_smooth (ε:ℝ) (hε:0<ε) :
    ContDiff ℝ ∞ (reciprocalSquareRegularizer ε) := by
  apply ContDiff.inv (contDiff_id.pow 2 |>.add contDiff_const)
  intro x
  positivity

theorem reciprocal_square_regularizer_deriv (ε:ℝ) (hε:0<ε) :
    deriv (reciprocalSquareRegularizer ε) =
      fun x => ((-2*x)*reciprocalSquareRegularizer ε x)*reciprocalSquareRegularizer ε x := by
  funext x
  have h := (((hasDerivAt_id x).pow 2).add_const ε).inv (by positivity : x^2+ε≠0)
  have hh := h.deriv
  change deriv (reciprocalSquareRegularizer ε) x = _ at hh
  rw [hh]
  dsimp [reciprocalSquareRegularizer]
  field_simp

theorem reciprocal_square_regularizer_growth (ε:ℝ) (hε:0<ε) (k:ℕ) :
    ∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x:ℝ,
      ‖iteratedFDeriv ℝ k (reciprocalSquareRegularizer ε) x‖≤C*(1+‖x‖)^a := by
  have hf := reciprocal_square_regularizer_smooth ε hε
  have hlin := linear_map_all_derivatives_growth ((-2:ℝ) • ContinuousLinearMap.id ℝ ℝ)
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      refine ⟨ε⁻¹,by positivity,0,fun x => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      simp only [pow_zero,mul_one,reciprocalSquareRegularizer,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (by positivity : 0<x^2+ε))]
      exact inv_anti₀ hε (by nlinarith [sq_nonneg x])
    | succ n =>
      have hb : ∀i:ℕ,i≤n → ∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x:ℝ,
          ‖iteratedFDeriv ℝ i (reciprocalSquareRegularizer ε) x‖≤C*(1+‖x‖)^a :=
        fun i hi => ih i (by omega)
      have hfirst : ∀i:ℕ,i≤n → ∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x:ℝ,
          ‖iteratedFDeriv ℝ i (fun y => (-2*y)*reciprocalSquareRegularizer ε y) x‖≤C*(1+‖x‖)^a := by
        intro i hi
        apply finite_iterated_polynomial_growth_mul (fun y:ℝ => -2*y)
          (reciprocalSquareRegularizer ε) (by fun_prop) hf i
        · intro j hj
          exact hlin j
        · intro j hj
          exact hb j (hj.trans hi)
      obtain ⟨C,hC,a,ha⟩ := finite_iterated_polynomial_growth_mul
        (fun y => (-2*y)*reciprocalSquareRegularizer ε y) (reciprocalSquareRegularizer ε)
        ((contDiff_const.mul contDiff_id).mul hf) hf n hfirst hb
      refine ⟨C,hC,a,fun x => ?_⟩
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_succ',
        reciprocal_square_regularizer_deriv ε hε,← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact ha x
end Asakura.Chapter12
#print axioms Asakura.Chapter12.reciprocal_square_regularizer_growth
