import Chapter8WeightedRandomIntegral

open MeasureTheory Set
open scoped ENNReal NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Apply weighted Cauchy--Schwarz to an operator kernel dominated by k.
Square integrability of the normalized kernel is derived from that of H. -/
theorem weighted_operator_moment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (k : ℝ → ℝ≥0) (hk : Measurable k) (hkp : ∀ s,0<k s) (hk1 : ∀ᵐ s ∂μ,k s≤1)
    (K : ℝ → E →L[ℝ] E) (hK : Continuous K) (hKb : ∀ᵐ s ∂μ,‖K s‖≤(k s:ℝ))
    (H : Ω × ℝ → E) (hH : Measurable H) (h2 : MemLp H 2 (P.prod μ))
    (C : ℝ) (hb : ∀ᵐ s ∂μ,(∫ w,‖H (w,s)‖^2 ∂P)≤C) :
    MemLp (fun w => ∫ s,K s (H (w,s)) ∂μ) 2 P ∧
      (∫ w,‖∫ s,K s (H (w,s)) ∂μ‖^2 ∂P)≤(∫ s,(k s:ℝ) ∂μ)^2*C := by
  let ν := μ.withDensity (fun s => (k s:ℝ≥0∞))
  have hν : ν≤μ := by
    have hh : (fun s => (k s:ℝ≥0∞))≤ᵐ[μ](fun _ => (1:ℝ≥0∞)) := hk1.mono (fun s hs => by
      change (k s:ℝ≥0∞)≤1
      exact_mod_cast hs)
    have hh' : ν≤μ.withDensity (1 : ℝ → ℝ≥0∞) := withDensity_mono hh
    simpa only [withDensity_one] using hh'
  have hki : (∫⁻ s,(k s:ℝ≥0∞) ∂μ)<∞ := by
    have hh := lintegral_mono_ae (hk1.mono (fun s hs => show (k s:ℝ≥0∞)≤1 by exact_mod_cast hs))
    exact hh.trans_lt (by simp)
  let F := fun z : Ω × ℝ => (k z.2:ℝ)⁻¹ • K z.2 (H z)
  have hFm : Measurable F := ((hk.coe_nnreal_real.comp measurable_snd).inv).smul
    (((hK.comp continuous_fst).clm_apply continuous_snd).measurable.comp (measurable_snd.prodMk hH))
  have hbound s (hs : ‖K s‖≤(k s:ℝ)) w : ‖F (w,s)‖≤‖H (w,s)‖ := by
    have hp : 0<(k s:ℝ) := hkp s
    dsimp only [F]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    have hh := mul_le_mul_of_nonneg_left (((K s).le_opNorm (H (w,s))).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg (H (w,s))))) (inv_nonneg.mpr hp.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hh
  have hF2 : MemLp F 2 (P.prod ν) := by
    apply (h2.mono_measure (Measure.prod_mono le_rfl hν)).of_le hFm.aestronglyMeasurable
    rw [Measure.ae_prod_iff_ae_ae] <;> try exact measurableSet_le hFm.norm hH.norm
    apply ae_of_all
    intro w
    exact (Measure.absolutelyContinuous_of_le hν).ae_le (hKb.mono (fun s hs => hbound s hs w))
  have hHi := h2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hFB : ∀ᵐ s ∂μ,(∫ w,‖F (w,s)‖^2 ∂P)≤C := by
    filter_upwards [hKb,hb,hHi.prod_left_ae] with s hs hb hi
    have hm : Measurable (fun w => ‖F (w,s)‖^2) := (hFm.comp measurable_prodMk_right).norm.pow_const 2
    have hf : Integrable (fun w => ‖F (w,s)‖^2) P := by
      apply hi.mono' hm.aestronglyMeasurable
      apply ae_of_all
      intro w
      simpa only [Real.norm_eq_abs,abs_sq] using
        (pow_le_pow_left₀ (norm_nonneg (F (w,s))) (hbound s hs w) 2)
    exact (integral_mono hf hi (fun w => pow_le_pow_left₀ (norm_nonneg _) (hbound s hs w) 2)).trans hb
  have hh := weighted_random_integral_bound P μ k hk hki F hFm hF2 C hFB
  have he w : (fun s => (k s:ℝ) • F (w,s))=(fun s => K s (H (w,s))) := by
    funext s
    dsimp only [F]
    rw [smul_smul,mul_inv_cancel₀ (show (k s:ℝ)≠0 from (show 0<(k s:ℝ) from hkp s).ne'),one_smul]
  simpa only [he] using hh
end Asakura.Chapter8
