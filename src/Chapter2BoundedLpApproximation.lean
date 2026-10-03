import Chapter2LpExponentLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The real power integral is the real value of the nonnegative integral
appearing in the Lp seminorm. -/
theorem power_integral_eq_lintegral_enorm
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (f : S → ℝ)
    (hf : AEStronglyMeasurable f μ) (p : ℝ) (hp : 0 ≤ p) :
    (∫ x, |f x| ^ p ∂μ) = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) p)
    ((Real.continuous_rpow_const hp).comp_aestronglyMeasurable hf.norm)]
  congr 1
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp]
  congr 1
  simpa only [Real.norm_eq_abs] using ofReal_norm (f x)

/-- On a finite measure space, bounded square errors tending to zero
have pth-power integrals tending to zero for every positive finite p.
The lower-exponent branch uses Holder; the upper branch uses the printed
bounded-error estimate. -/
theorem bounded_square_limit_all_exponents
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (f : ℕ → S → ℝ) (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ C)
    (hlim : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, |f n x| ^ p ∂μ) atTop (𝓝 0) := by
  have h2 n : MemLp (f n) 2 μ := MemLp.of_bound (hm n) C (by simpa only [Real.norm_eq_abs] using hb n)
  have hi n : Integrable (fun x => f n x ^ 2) μ := (memLp_two_iff_integrable_sq (hm n)).1 (h2 n)
  by_cases hp2 : p ≤ 2
  · have he (n) : eLpNorm' (f n) 2 μ = ENNReal.ofReal ((∫ x, f n x ^ 2 ∂μ) ^ (2:ℝ)⁻¹) := by
      have h := (h2 n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) (hm n)] at h
      simpa only [ENNReal.toReal_ofNat,Real.norm_eq_abs,Real.rpow_two,sq_abs] using h
    have hnorm : Tendsto (fun n => eLpNorm' (f n) 2 μ) atTop (𝓝 0) := by
      simp_rw [he]
      have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hlim.rpow_const (Or.inr (by norm_num : 0 ≤ (2:ℝ)⁻¹)))
      simp only [Real.zero_rpow (by norm_num : (2:ℝ)⁻¹ ≠ 0),ENNReal.ofReal_zero] at ht
      convert ht using 1
      funext n
      rfl
    have hlp := finite_measure_lower_exponent_limit μ f hm p hp hp2 hnorm
    have hpow := hlp.ennrpow_const p
    simp only [ENNReal.zero_rpow_of_pos hp] at hpow
    have ht := (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).comp hpow
    simp only [ENNReal.toReal_zero] at ht
    convert ht using 1
    funext n
    rw [power_integral_eq_lintegral_enorm μ (f n) (hm n) p hp.le,
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hp]
    rfl
  · exact bounded_higher_exponent_integral_limit μ f hm hi C p hC (not_le.1 hp2).le hb hlim

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.power_integral_eq_lintegral_enorm
#print axioms Asakura.Chapter2Complete.bounded_square_limit_all_exponents
