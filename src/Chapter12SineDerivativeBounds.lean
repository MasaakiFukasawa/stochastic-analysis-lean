import Chapter12LinearCylinder
import Chapter12Unbounded
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open MeasureTheory Set
open scoped ContDiff ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every derivative of sine and cosine is bounded by one. -/
theorem trigonometric_iterated_derivative_bound (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n Real.sin x‖ ≤ 1 ∧ ‖iteratedDeriv n Real.cos x‖ ≤ 1 := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero, Real.norm_eq_abs] using
      And.intro (Real.abs_sin_le_one x) (Real.abs_cos_le_one x)
  | succ n ih =>
    rw [Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_add_one_cos]
    simpa only [Pi.neg_apply,norm_neg] using And.intro ih.2 ih.1

/-- Composing sine with a linear coordinate and scaling preserves the
polynomial-growth condition at every order in the cylinder definition. -/
theorem scaled_sine_linear_all_derivatives_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (a : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ b : ℕ, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => a*Real.sin (L y)) x‖ ≤ C*(1+‖x‖)^b := by
  refine ⟨|a| *‖L‖^k,mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) _),0,fun x => ?_⟩
  simp only [pow_zero,mul_one]
  change ‖iteratedFDeriv ℝ k (fun y => a • (Real.sin ∘ L) y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (((Real.contDiff_sin (n := ∞)).comp L.contDiff).of_le (by simp)).contDiffAt,
    norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
  change ‖iteratedFDeriv ℝ k (Real.sin ∘ L) x‖ ≤ ‖L‖^k
  rw [L.iteratedFDeriv_comp_right (Real.contDiff_sin (n := ∞)) x (by simp)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k Real.sin (L x)‖*(∏ _ : Fin k, ‖L‖) :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ 1*‖L‖^k := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact (trigonometric_iterated_derivative_bound k (L x)).1) (pow_nonneg (norm_nonneg _) _)
    _ = _ := one_mul _

end Asakura.Chapter12
