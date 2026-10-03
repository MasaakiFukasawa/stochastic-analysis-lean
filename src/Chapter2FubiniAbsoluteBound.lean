import Chapter2SignedIntegralContinuity
import Chapter2SquareRootCS
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The bound is for the total-variation integral itself, as needed for
ordinary Fubini, not merely for the absolute signed integral. -/
theorem signed_stieltjes_absolute_integral_bound
    (α β : Measure ℝ) [IsFiniteMeasure α] [IsFiniteMeasure β] (ν : SignedMeasure ℝ)
    (hc : ∀ s t, s ≤ t → |ν (Ioc s t)| ≤ Real.sqrt (α.real (Ioc s t))*Real.sqrt (β.real (Ioc s t)))
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable (fun r => f r^2) α) :
    Integrable f ν.totalVariation ∧ (∫ r, |f r| ∂ν.totalVariation) ≤
      Real.sqrt (∫ r, f r^2 ∂α)*Real.sqrt (β.real univ) := by
  have hi := (signed_stieltjes_single_integral_bound α β ν hc f hf hfi).1
  have h := stieltjes_integral_real_intervals α β ν hc f (fun _ => 1) hf measurable_const
  simp only [mul_one,one_pow] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (.of_forall fun r => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_const (1:ℝ)) (.of_forall fun _ => zero_le_one),
    integral_const,smul_eq_mul,mul_one] at h
  have hfinite : (ENNReal.ofReal (∫ r, f r^2 ∂α))^(1/2:ℝ)*
      (ENNReal.ofReal (β.real univ))^(1/2:ℝ) < ∞ := by finiteness
  have ht := ENNReal.toReal_mono hfinite.ne h
  rw [← ofReal_integral_eq_lintegral_ofReal hi.abs (.of_forall fun r => abs_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun r => abs_nonneg _),ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow,← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg fun r => sq_nonneg _),
    ENNReal.toReal_ofReal (measureReal_nonneg)] at ht
  exact ⟨hi,by simpa only [← Real.sqrt_eq_rpow] using ht⟩

/-- The expectation and parameter-integration steps in the printed Fubini
proof. A pathwise KW bound implies absolute integrability on E×Ω and the
mixed L1(L2) bound; no expectation of absolute covariation is assumed. -/
theorem fubini_kw_expectation_bound
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (μ : Measure E) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (A V : E × Ω → ℝ) (B : Ω → ℝ) (hV : Measurable V)
    (hV0 : ∀ z, 0 ≤ V z)
    (hAi : ∀ᵐ x ∂μ, Integrable (fun ω => A (x,ω)) P)
    (hA0 : ∀ᵐ x ∂μ, ∀ᵐ ω ∂P, 0 ≤ A (x,ω))
    (hBi : Integrable B P) (hB0 : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hkw : ∀ᵐ x ∂μ, ∀ᵐ ω ∂P, V (x,ω) ≤ Real.sqrt (A (x,ω))*Real.sqrt (B ω))
    (hN : Integrable (fun x => Real.sqrt (∫ ω, A (x,ω) ∂P)) μ) :
    Integrable V (μ.prod P) ∧
      (∫ z, V z ∂μ.prod P) ≤
        (∫ x, Real.sqrt (∫ ω, A (x,ω) ∂P) ∂μ)*Real.sqrt (∫ ω, B ω ∂P) := by
  have hx : ∀ᵐ x ∂μ, Integrable (fun ω => V (x,ω)) P ∧
      (∫ ω, V (x,ω) ∂P) ≤ Real.sqrt (∫ ω, A (x,ω) ∂P)*Real.sqrt (∫ ω, B ω ∂P) := by
    filter_upwards [hAi,hA0,hkw] with x hai ha0 hki
    obtain ⟨hprod,hbound⟩ := integrable_sqrt_product_bound P (fun ω => A (x,ω)) B hai hBi ha0 hB0
    have hvi : Integrable (fun ω => V (x,ω)) P := hprod.mono'
      ((hV.comp measurable_prodMk_left).aestronglyMeasurable)
      (hki.mono (fun ω hω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hV0 (x,ω))] using hω))
    exact ⟨hvi,(integral_mono_ae hvi hprod hki).trans hbound⟩
  have hvnorm : (fun x => ∫ ω, ‖V (x,ω)‖ ∂P) = (fun x => ∫ ω, V (x,ω) ∂P) := by
    funext x
    apply integral_congr_ae
    exact .of_forall (fun ω => by dsimp only; rw [Real.norm_eq_abs,abs_of_nonneg (hV0 (x,ω))])
  have hb := hN.mul_const (Real.sqrt (∫ ω, B ω ∂P))
  have hi : Integrable (fun x => ∫ ω, V (x,ω) ∂P) μ := hb.mono'
    (hV.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
    (hx.mono (fun x hxx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun ω => hV0 (x,ω)))]
      exact hxx.2))
  have hiv : Integrable V (μ.prod P) := (integrable_prod_iff hV.aestronglyMeasurable).mpr
    ⟨hx.mono (fun x hxx => hxx.1),by rw [hvnorm]; exact hi⟩
  refine ⟨hiv,?_⟩
  rw [integral_prod V hiv,← integral_mul_const]
  exact integral_mono_ae hi hb (hx.mono (fun x hxx => hxx.2))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_stieltjes_absolute_integral_bound
#print axioms Asakura.Chapter2Complete.fubini_kw_expectation_bound
