import Chapter6GaussianBridgeResidual
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- The singular majorant for the Kyle order rate is integrable all the way to
maturity, although its square is not. -/
theorem terminal_inverse_sqrt_integrable (T : ℝ) :
    IntervalIntegrable (fun t => (T-t)^(-1/2:ℝ)) volume 0 T := by
  have h := (intervalIntegral.intervalIntegrable_rpow'
    (by norm_num : (-1:ℝ)< -1/2) (a := 0) (b := T)).comp_sub_left T
  simpa only [sub_zero,sub_self] using h.symm

/-- Tonelli plus the second-moment bound gives absolute time integrability
almost surely; no square-integrability of the time-dependent order rate is used. -/
theorem order_rate_integrable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure S) [SFinite ν]
    (a : S → Ω → ℝ) (b : S → ℝ)
    (hm : AEStronglyMeasurable (Function.uncurry a) (ν.prod P))
    (h2 : ∀ t, MemLp (a t) 2 P) (hb : Integrable b ν)
    (hbound : ∀ᵐ t ∂ν, Real.sqrt (∫ w,(a t w)^2 ∂P) ≤ b t) :
    Integrable (Function.uncurry a) (ν.prod P) ∧
      ∀ᵐ w ∂P, Integrable (fun t => a t w) ν := by
  have hnorm : Integrable (fun t => ∫ w, ‖a t w‖ ∂P) ν := by
    apply hb.mono' hm.norm.integral_prod_right'
    filter_upwards [hbound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun w => norm_nonneg _))]
    have hs := Asakura.Chapter6.integral_le_sqrt_second_moment P
      (fun w => ‖a t w‖) (h2 t).norm
    simp only [Real.norm_eq_abs, sq_abs] at hs
    exact hs.trans ht
  have hi : Integrable (Function.uncurry a) (ν.prod P) :=
    (integrable_prod_iff hm).mpr ⟨Eventually.of_forall (fun t => (h2 t).integrable (by norm_num)),hnorm⟩
  exact ⟨hi,hi.prod_left_ae⟩

end Asakura.Chapter10
