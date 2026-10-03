import Chapter5CumulativeStieltjesIntegral
import Chapter5ContinuousMultiplier

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_multiplier_integrable (b : ℝ) (hb : 0 ≤ b)
    (μ : Measure ℝ) (hs : ∀ᵐ r ∂μ, r ∈ Icc 0 b)
    (H G : ℝ → ℝ) (hH : ContinuousOn H (Icc 0 b)) (hm : Measurable H)
    (hi : Integrable G μ) : Integrable (fun r => H r*G r) μ := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  apply (hi.norm.const_mul C).mono' (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  filter_upwards [hs] with r hr
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC r hr) (norm_nonneg _)

/-- Convert a constructed variation integral against an absolutely
continuous bracket to the weighted Lebesgue integral, at any finite time. -/
theorem time_density_variation_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (B J : ClosedTime T → Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hB : ∀ n, ∀ᵐ w ∂P, ∀ r ∈ Icc 0 (c n), B (realTimeClamp r) w = ∫ s in 0..r, G (w,s))
    (hGm : ∀ w, Measurable (fun r => G (w,r)))
    (hGi : ∀ n, ∀ᵐ w ∂P, IntervalIntegrable (fun r => G (w,r)) volume 0 (c n))
    (hHm : ∀ w, Measurable (fun r => H (w,r)))
    (hHc : ∀ n w, ContinuousOn (fun r => H (w,r)) (Icc 0 (c n)))
    (hJ : VariationIntegralFormula P c hc B H J)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    J (realTimeClamp d) =ᵐ[P] fun w => ∫ r in 0..d, H (w,r)*G (w,r) := by
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]; exact hdT
  obtain ⟨j,hj⟩ := hcc _ hdt
  have hdj : d ≤ c j := by
    change (realTimeClamp d : EReal) < (realTimeClamp (c j) : EReal) at hj
    rw [real_time_clamp_eq d hd hdT.le,real_time_clamp_eq (c j) (hc j) (hcT j).le] at hj
    exact EReal.coe_le_coe_iff.mp hj.le
  obtain ⟨κ,_,hκ,hHi,hform⟩ := hJ j
  filter_upwards [hκ,hHi,hform,hB j,hGi j] with w hκw hHiw hfw hBw hGiw
  have hprod : Integrable (fun r => H (w,r)*G (w,r)) (volume.restrict (Ioc 0 (c j))) := by
    apply continuous_multiplier_integrable (c j) (hc j) _ _ _ _ (hHc j w) (hHm w) hGiw.1
    exact (ae_restrict_mem measurableSet_Ioc).mono fun r hr => ⟨hr.1.le,hr.2⟩
  have hp : IntervalIntegrable (fun r => (Iic d).indicator (fun r => H (w,r)) r*G (w,r)) volume 0 (c j) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (hc j)).mpr
    have heq : (fun r => (Iic d).indicator (fun r => H (w,r)) r*G (w,r)) =
        (Iic d).indicator (fun r => H (w,r)*G (w,r)) := by
      funext r
      by_cases hr : r ∈ Iic d <;> simp [hr,Set.indicator]
    rw [heq]
    exact hprod.indicator measurableSet_Iic
  have he := cumulative_stieltjes_density_integral (c j) (hc j) (fun r => G (w,r))
    ((Iic d).indicator (fun r => H (w,r))) (hGm w) ((hHm w).indicator measurableSet_Iic)
    hGiw (κ w) (hHiw.indicator measurableSet_Iic) hp (by
      intro s t hst
      rw [hκw s t hst,hBw _ (intervalClamp_mem _ _ _ _),hBw _ (intervalClamp_mem _ _ _ _)])
  have hf := hfw (realTimeClamp d)
  rw [min_eq_right (real_time_clamp_mono hdj),finite_prefix_time_of_real (c j) d (hc j) ⟨hd,hdj⟩ (hcT j).le] at hf
  change J (realTimeClamp d) w = signedIntegralRaw (κ w) ((Iic d).indicator (fun r => H (w,r))) at hf
  rw [hf,he,intervalIntegral.integral_of_le (hc j)]
  have hfun : (fun r => (Iic d).indicator (fun r => H (w,r)) r*G (w,r)) =
      (Iic d).indicator (fun r => H (w,r)*G (w,r)) := by
    funext r; by_cases hr : r ∈ Iic d <;> simp [hr,Set.indicator]
  rw [hfun,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioc_of_le hdj,intervalIntegral.integral_of_le hd]

end Asakura.Chapter5
