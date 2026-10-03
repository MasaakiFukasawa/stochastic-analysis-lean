import Chapter2ItoAssociativity
import Chapter2ContinuousIntegrand
import Chapter5HeatGradient

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Local continuity of a multiplier preserves the actual square-energy
condition. No boundedness uniform in the sample point is required. -/
theorem continuous_multiplier_square_integrable (b : ℝ) (hb : 0 ≤ b)
    (μ : Measure ℝ) (hs : ∀ᵐ r ∂μ, r ∈ Icc 0 b)
    (H G : ℝ → ℝ) (hH : ContinuousOn H (Icc 0 b)) (hm : Measurable H)
    (hi : Integrable (fun r => G r^2) μ) :
    Integrable (fun r => (H r*G r)^2) μ := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  have hCm : 0 ≤ C := (norm_nonneg (H 0)).trans (hC 0 (left_mem_Icc.mpr hb))
  have hmp : AEStronglyMeasurable (fun r => (H r*G r)^2) μ := by
    convert ((hm.aestronglyMeasurable.pow 2).mul hi.aestronglyMeasurable) using 1
    funext r
    simp only [Pi.mul_apply,Pi.pow_apply,mul_pow]
  apply (hi.const_mul (C^2)).mono' hmp
  filter_upwards [hs] with r hr
  change |(H r*G r)^2| ≤ C^2*G r^2
  rw [abs_of_nonneg (sq_nonneg _),mul_pow]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (H r)) (hC r hr) 2)
    (sq_nonneg _)

/-- Compose an arbitrary progressive Ito integrand with a continuous
adapted multiplier, constructing the product integral before applying
associativity. This allows Borel diffusion coefficients in the PDE step. -/
theorem continuous_multiplier_ito_composition
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (X A Y Z : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hA : LocalCovarianceWitness P F X X A)
    (hY : LocalMProcessWitness P F Y) (hZ : LocalMProcessWitness P F Z)
    (c : ℕ → ℝ) (hc : ∀ n, 0 < c n) (hcm : StrictMono c) (hcT : ∀ n, (c n:EReal) < T)
    (hct : StrictMono (fun n => realTimeClamp (T := T) (c n)))
    (hcut : ∀ n, realTimeClamp (T := T) (c n) < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hAm : ∀ n w, MonotoneOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)))
    (hAc : ∀ n w, ContinuousOn (fun r => A (realTimeClamp r) w) (Icc 0 (c n)))
    (G H : Ω × ℝ → ℝ)
    (hGm : ∀ w, Measurable (fun r => G (w,r))) (hHm : ∀ w, Measurable (fun r => H (w,r)))
    (hG : ∀ n, @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => G (z.1,z.2.val)))
    (hHa : ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → Measurable[F (realTimeClamp r)] (fun w => H (w,r)))
    (hHc : ∀ n w, ContinuousOn (fun r => H (w,r)) (Icc 0 (c n)))
    (hi : ∀ n, ∀ᵐ w ∂P, Integrable (fun r => G (w,r)^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure)
    (hy : ItoCovarianceFormula P F X G Y) (hz : ItoCovarianceFormula P F Y H Z) :
    ∃ W : ClosedTime T → Ω → ℝ,
      LocalMProcessWitness P F W ∧ ItoCovarianceFormula P F X (fun z => H z*G z) W ∧
      (∀ᵐ w ∂P, ∀ t, t < ⊤ → Z t w = W t w) := by
  have hp n := continuous_adapted_real_progressive F hF H (c n) (hc n).le
    (fun r hr => hHa r hr.1 ((EReal.coe_le_coe hr.2).trans_lt (hcT n))) (hHc n)
  have hip n : ∀ᵐ w ∂P, Integrable (fun r => (H (w,r)*G (w,r))^2)
      (intervalStieltjes 0 (c n) (hc n).le (fun r => A (realTimeClamp r) w) (hAm n w)
        (fun r hr => (hAc n w r hr).mono inter_subset_left)).measure := by
    filter_upwards [hi n] with w hw
    apply continuous_multiplier_square_integrable (c n) (hc n).le _ _ _ _ (hHc n w) (hHm w) hw
    exact (interval_stieltjes_ae_mem_Ioc _ _ _ _ _ _).mono fun r hr => ⟨hr.1.le,hr.2⟩
  obtain ⟨W,hW,hWI⟩ := ito_integral_exists_with_covariance_characterization
    P hT F hF hle hnull X A hX hA c hc hcm hcT hct hcut hcc hAm hAc
    (fun z => H z*G z) (fun n => (hp n).mul (hG n)) hip
  exact ⟨W,hW,hWI,ito_integral_associativity P hT F hF hle hnull X Y Z W G H
    hX hY hZ hW hGm hHm hy hz hWI⟩

end Asakura.Chapter5
