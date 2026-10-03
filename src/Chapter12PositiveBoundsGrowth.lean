import Chapter12AffineHigherBounds
import Mathlib.Analysis.Calculus.MeanValue

open scoped ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem positive_derivative_bounds_polynomial {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hb : ∀k:ℕ,1≤k → ∃C:ℝ,0≤C ∧ ∀x,‖iteratedFDeriv ℝ k f x‖≤C) :
    ∀k:ℕ,∃C:ℝ,0≤C ∧ ∃a:ℕ,∀x,‖iteratedFDeriv ℝ k f x‖≤C*(1+‖x‖)^a := by
  intro k
  by_cases hk : k=0
  · subst k
    obtain ⟨C,hC,hbC⟩ := hb 1 le_rfl
    have hLip : LipschitzWith ⟨C,hC⟩ f := by
      apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
      intro x
      have hh : ‖fderiv ℝ f x‖≤C := by simpa only [norm_iteratedFDeriv_one] using hbC x
      exact_mod_cast hh
    refine ⟨‖f 0‖+C,add_nonneg (norm_nonneg _) hC,1,?_⟩
    intro x
    rw [norm_iteratedFDeriv_zero,pow_one]
    have hh := hLip.norm_sub_le x 0
    change ‖f x-f 0‖≤C*‖x-0‖ at hh
    rw [sub_zero] at hh
    have hn := norm_add_le (f x-f 0) (f 0)
    rw [sub_add_cancel] at hn
    nlinarith [norm_nonneg (f 0),norm_nonneg x]
  · obtain ⟨C,hC,hbC⟩ := hb k (by omega)
    exact ⟨C,hC,0,fun x => by simpa only [pow_zero,mul_one] using hbC x⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.positive_derivative_bounds_polynomial
