import Chapter3VariationIntegrandCongruence
import Chapter2SignedDifferenceIntegral
import Chapter2VariationCumulativeIdentification
import Chapter2StieltjesRestriction

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem signed_integral_positive_measure
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (f : S → ℝ) (hf : Integrable f μ) :
    signedIntegralRaw μ.toSignedMeasure f = ∫ x, f x ∂μ := by
  simpa using signed_difference_integral μ (0 : Measure S) f (by simpa using hf)

/-- Evaluate an already constructed variation integral at any finite
real time using the positive Stieltjes measure on that shorter interval. -/
theorem positive_variation_integral_at_time
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hAm : ∀ n ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hAc : ∀ n ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)))
    (hI : VariationIntegralFormula P c hc A H I)
    (j : ℕ) (d : ℝ) (hd : 0 ≤ d) (hdc : d ≤ c j)
    (hAdm : ∀ ω, MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 d))
    (hAdc : ∀ ω, ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 d)) :
    I (realTimeClamp d) =ᵐ[P] fun ω => ∫ r, H (ω,r)
      ∂(intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hAdm ω)
        (fun r hr => (hAdc ω r hr).mono inter_subset_left)).measure := by
  obtain ⟨ν,hs,hν,hi,hform⟩ := hI j
  filter_upwards [hν,hi,hform] with ω hνω hiω hfω
  let μ := (intervalStieltjes 0 (c j) (hc j) (fun r => A (realTimeClamp r) ω) (hAm j ω)
    (fun r hr => (hAc j ω r hr).mono inter_subset_left)).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
  have heν : ν ω = μ.toSignedMeasure := by
    apply signed_measure_ext_Ioc
    intro a b hab
    rw [hνω a b hab.le,Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      intervalStieltjes_Ioc_real _ _ _ _ _ _ a b hab.le]
  have hiμ : Integrable (fun r => H (ω,r)) μ := by
    rw [heν,SignedMeasure.totalVariation_eq_variation,Measure.variation_toSignedMeasure] at hiω
    exact hiω
  have he := hfω (realTimeClamp d)
  rw [min_eq_right (real_time_clamp_mono hdc),finite_prefix_time_of_real (c j) d (hc j)
    ⟨hd,hdc⟩ (hcT j).le] at he
  change I (realTimeClamp d) ω = signedIntegralRaw (ν ω) ((Iic d).indicator (fun r => H (ω,r))) at he
  rw [heν,signed_integral_positive_measure μ _ (hiμ.indicator measurableSet_Iic),integral_indicator measurableSet_Iic] at he
  rw [interval_stieltjes_restrict_Iic 0 (c j) d hd hdc (fun r => A (realTimeClamp r) ω)
    (hAm j ω) (fun r hr => (hAc j ω r hr).mono inter_subset_left)
    (hAdm ω) (fun r hr => (hAdc ω r hr).mono inter_subset_left)]
  exact he

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.signed_integral_positive_measure
#print axioms Asakura.Chapter3Complete.positive_variation_integral_at_time
