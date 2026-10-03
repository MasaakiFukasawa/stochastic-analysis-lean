import ManuscriptLinearity
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Asakura

/-- app0:570--598: |f_n-f| <= 2g; Fatou for 2g-|f_n-f|;
then the integral triangle inequality. -/
theorem manuscript_dominated_convergence {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (F g : Ω → ℝ)
    (hf : ∀ n, Measurable (f n)) (hF : Measurable F) (hg : Measurable g)
    (hgi : Integrable g μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  have hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ g x := by
    filter_upwards [ae_all_iff.mpr hbound,hlim] with x hx ht
    exact le_of_tendsto' ht.norm hx
  have hFi : Integrable F μ := hgi.mono' hF.aestronglyMeasurable hFb
  have hfi : ∀ n, Integrable (f n) μ := fun n => hgi.mono' (hf n).aestronglyMeasurable (hbound n)
  let E : ℕ → Ω → ℝ≥0∞ := fun n x => ‖f n x-F x‖ₑ
  let G : Ω → ℝ≥0∞ := fun x => ‖(2:ℝ)*g x‖ₑ
  have hEb : ∀ n, E n ≤ᵐ[μ] G := by
    intro n
    filter_upwards [hbound n,hFb] with x hn hx
    have hr : ‖f n x-F x‖ ≤ ‖(2:ℝ)*g x‖ := by
      have ht := norm_sub_le (f n x) (F x)
      have ha := le_abs_self (2*g x)
      simp only [Real.norm_eq_abs] at hn hx ht ⊢
      linarith
    simpa [E,G,← ofReal_norm] using ENNReal.ofReal_le_ofReal hr
  have hGt : (∫⁻ x, G x ∂μ) ≠ ⊤ := (hgi.const_mul 2).hasFiniteIntegral.ne
  have hEt : ∀ᵐ x ∂μ, Tendsto (fun n => E n x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa [E] using (hx.sub_const (F x)).enorm
  have hEI := manuscript_dominated_zero E G (fun n => ((hf n).sub hF).enorm)
    (hg.const_mul 2 |>.enorm) hEb hGt hEt
  have hreal : Tendsto (fun n => (∫⁻ x, E n x ∂μ).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEI
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ hreal
  intro n
  rw [← manuscript_real_integral_sub μ (f n) F (hf n) hF (hfi n) hFi]
  simpa only [E,ofReal_norm] using norm_integral_le_lintegral_norm (μ := μ) (fun x => f n x-F x)

end Asakura
