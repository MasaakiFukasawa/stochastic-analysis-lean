import Chapter12BrownianMaximumTail
import Chapter12ExponentialTailMoment
import Chapter12ContinuousPathSigma

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- All exponential moments of the Brownian path maximum follow by
integrating the Doob tail estimate, as in the manuscript. -/
theorem brownian_path_exponential_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (c : ℝ) : Integrable (fun w => Real.exp (c*‖X w‖)) P := by
  by_cases hcp : 0 < c
  · apply exponential_moment_of_tail P (fun w => ‖X w‖) hXm.norm
      (fun w => norm_nonneg _) (2*Real.exp ((2*c)^2*T/2)) (2*c) c
      (by positivity) hcp (by linarith)
    intro t ht
    have hb := brownian_path_norm_tail P B hB hm hc T X he (2*c) t (by linarith) ht
    convert hb using 2
    rw [Real.exp_add]
    ring
  · apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all P fun w => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hcp) (norm_nonneg _))

/-- These moments also give membership of every finite Lp space for each
exponential bound used in the stock and inverse-denominator estimates. -/
theorem brownian_path_exponential_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ w, Continuous (fun t => B t w)) (T : ℝ≥0)
    (X : Ω → C(Icc (0:ℝ) T,ℝ)) (hXm : Measurable X)
    (he : ∀ w (s : Icc (0:ℝ) T), X w s = B ⟨s.val,s.property.1⟩ w)
    (c : ℝ) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun w => Real.exp (c*‖X w‖)) p P := by
  by_cases hp0 : p = 0
  · subst p
    exact memLp_zero_iff_aestronglyMeasurable.mpr (by fun_prop)
  apply (integrable_norm_rpow_iff (by fun_prop) hp0 hp).mp
  have hi := brownian_path_exponential_moment P B hB hm hc T X hXm he (c*p.toReal)
  convert hi using 1
  funext w
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_mul]
  congr 1
  ring

end Asakura.Chapter12
