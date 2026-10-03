import Chapter3PositiveVariationIntegral
import Chapter4BrownianTimeMeasure

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false

/-- If the integrator equals time, its constructed variation integral is
the ordinary time integral. No formula for that integral is postulated. -/
theorem clock_variation_integral_at_time
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → A (realTimeClamp r) ω = r)
    (hI : VariationIntegralFormula P c hc A H I)
    (j : ℕ) (d : ℝ) (hd : 0 ≤ d) (hdc : d ≤ c j) :
    I (realTimeClamp d) =ᵐ[P] fun ω => ∫ r in 0..d, H (ω,r) := by
  have hAm n ω : MonotoneOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)) := by
    intro s hs t ht hst
    simpa only [hclock n ω s hs,hclock n ω t ht] using hst
  have hAc n ω : ContinuousOn (fun r => A (realTimeClamp r) ω) (Icc 0 (c n)) := by
    apply continuousOn_id.congr
    intro r hr
    exact hclock n ω r hr
  have hsub : Icc (0:ℝ) d ⊆ Icc 0 (c j) := Icc_subset_Icc_right hdc
  have hDm ω := (hAm j ω).mono hsub
  have hDc ω := (hAc j ω).mono hsub
  have he := positive_variation_integral_at_time P A I H c hc hcT hAm hAc hI
    j d hd hdc hDm hDc
  filter_upwards [he] with ω hω
  rw [hω]
  have hm : intervalStieltjes 0 d hd (fun r => A (realTimeClamp r) ω) (hDm ω)
      (fun r hr => (hDc ω r hr).mono inter_subset_left) =
      intervalStieltjes 0 d hd id (monotone_id.monotoneOn _)
        (fun _ _ => continuous_id.continuousWithinAt) := by
    apply StieltjesFunction.ext
    intro r
    exact hclock j ω _ (hsub (intervalClamp_mem 0 d hd r))
  rw [hm,clock_stieltjes_integral]


/-- The same identification simultaneously for every real time on every
finite prefix. The exceptional set is common, not chosen separately for t. -/
theorem clock_variation_integral_all_times
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hclock : ∀ n ω r, r ∈ Icc 0 (c n) → A (realTimeClamp r) ω = r)
    (hI : VariationIntegralFormula P c hc A H I) :
    ∀ᵐ ω ∂P, ∀ n d, d ∈ Icc 0 (c n) →
      I (realTimeClamp d) ω = ∫ r in 0..d, H (ω,r) := by
  apply ae_all_iff.mpr
  intro n
  obtain ⟨ν,_,hν,hi,hform⟩ := hI n
  filter_upwards [hν,hi,hform] with ω hνω hiω hfω
  let S := intervalStieltjes 0 (c n) (hc n) id (monotone_id.monotoneOn _)
    (fun _ _ => continuous_id.continuousWithinAt)
  let μ := S.measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite _ _ _ _ _ _
  have heν : ν ω = μ.toSignedMeasure := by
    apply signed_measure_ext_Ioc
    intro a b hab
    rw [hνω a b hab.le,Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      intervalStieltjes_Ioc_real _ _ _ _ _ _ a b hab.le]
    rw [hclock n ω _ (intervalClamp_mem _ _ _ _),hclock n ω _ (intervalClamp_mem _ _ _ _)]
    rfl
  have hiμ : Integrable (fun r => H (ω,r)) μ := by
    rw [heν,SignedMeasure.totalVariation_eq_variation,Measure.variation_toSignedMeasure] at hiω
    exact hiω
  intro d hd
  have he := hfω (realTimeClamp d)
  rw [min_eq_right (real_time_clamp_mono hd.2),finite_prefix_time_of_real (c n) d (hc n)
    hd (hcT n).le] at he
  change I (realTimeClamp d) ω = signedIntegralRaw (ν ω) ((Iic d).indicator (fun r => H (ω,r))) at he
  rw [heν,signed_integral_positive_measure μ _ (hiμ.indicator measurableSet_Iic),
    integral_indicator measurableSet_Iic] at he
  rw [he]
  change (∫ r in Iic d, H (ω,r) ∂S.measure) = _
  rw [show S.measure = volume.restrict (Ioc 0 (c n)) from clock_stieltjes_measure _ _ _,
    Measure.restrict_restrict measurableSet_Iic,Iic_inter_Ioc_of_le hd.2,
    intervalIntegral.integral_of_le hd.1]

end Asakura.Chapter4
