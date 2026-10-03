import Chapter3SignedStieltjesApproximation
import Chapter3StoppedOscillation
import Chapter2VariationIntegralFormula

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- Approximation of the actual signed finite-variation integral on a
finite prefix, with the increasing decomposition and measure identification
proved from A_loc. H need only be continuous on the original open domain. -/
theorem variation_integral_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A H I : ClosedTime T → Ω → ℝ) (hA : AdaptedLocalVariationWitness F A)
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcT : ∀ k, (c k:EReal) < T)
    (hI : VariationIntegralFormula P c hc A (fun z => H (realTimeClamp z.2) z.1) I)
    (τ : ℕ → ℕ → Ω → ClosedTime T) (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτ0 : ∀ n ω, τ n 0 ω = ⊥) (hτc : ∀ n ω t, t < ⊤ → ∃ N, t < τ n N ω)
    (hosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n) (k : ℕ) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω*
        (A (min (τ n (j+1) ω) (min (realTimeClamp (c k)) t)) ω-
         A (min (τ n j ω) (min (realTimeClamp (c k)) t)) ω))
      (fun t => I (min (realTimeClamp (c k)) t) ω) atTop := by
  let U := fun t ω => (pathVariation (fun s => A s ω) t+A t ω)/2
  let V := fun t ω => (pathVariation (fun s => A s ω) t-A t ω)/2
  obtain ⟨hU,hV,hm⟩ := local_variation_jordan_regular F hF A hA
  have hUm := finite_real_monotone_of_local U (fun ω => (hm ω).1) (c k) (hc k) (hcT k)
  have hVm := finite_real_monotone_of_local V (fun ω => (hm ω).2) (c k) (hc k) (hcT k)
  have hUr := (hU.real_interval_regular (c k) (hc k) (hcT k)).1
  have hVr := (hV.real_interval_regular (c k) (hc k) (hcT k)).1
  obtain ⟨ξ,hs,hξ,hi,hform⟩ := hI k
  have hdt : realTimeClamp (T := T) (c k) < ⊤ := by
    change (realTimeClamp (c k) : EReal) < T
    rw [real_time_clamp_eq _ (hc k) (hcT k).le]
    exact hcT k
  filter_upwards [hs,hξ,hform,hosc] with ω hsω hξω hfω hoω
  let Hs := fun t => H (min (realTimeClamp (c k)) t) ω
  have hHsc : Continuous Hs := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hHc ω _ ((min_le_left _ _).trans_lt hdt)).comp
      (continuous_const.min continuous_id).continuousAt
  let α := (intervalStieltjes 0 (c k) (hc k) (fun r => U (realTimeClamp r) ω) (hUm ω) (hUr ω)).measure
  let β := (intervalStieltjes 0 (c k) (hc k) (fun r => V (realTimeClamp r) ω) (hVm ω) (hVr ω)).measure
  letI : IsFiniteMeasure α := intervalStieltjes_finite _ _ _ _ _ _
  letI : IsFiniteMeasure β := intervalStieltjes_finite _ _ _ _ _ _
  have hmeasure : α.toSignedMeasure-β.toSignedMeasure = ξ ω := by
    apply signed_measure_ext_Ioc
    intro a b hab
    rw [VectorMeasure.sub_apply,Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
      intervalStieltjes_Ioc_real _ _ _ _ _ _ _ _ hab.le,
      intervalStieltjes_Ioc_real _ _ _ _ _ _ _ _ hab.le,hξω a b hab.le]
    dsimp only [U,V]
    ring
  have hdiff s (hs : s ≤ realTimeClamp (c k)) : A s ω = U s ω-V s ω := by
    dsimp only [U,V]
    ring
  have hos n j t ht hu : |Hs (τ n j ω)-Hs t| ≤ (1/2:ℝ)^n :=
    stopped_interval_oscillation (fun t => H t ω) (fun j => τ n j ω) (realTimeClamp (c k))
      ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hoω n) j t ht hu
  have hlim := signed_stieltjes_uniform_approximation (c k) (hc k) (hcT k)
    (fun t => U t ω) (fun t => V t ω) (fun t => A t ω) Hs
    (hUm ω) (hVm ω) (hUr ω) (hVr ω) hdiff
    (hHsc.comp real_time_clamp_continuous).measurable (fun _ _ => hHsc.continuousAt)
    (fun n j => τ n j ω) (fun n => hτm n ω) (fun n => hτ0 n ω) (fun n => hτc n ω)
    (fun n => (1/2:ℝ)^n) (fun n => pow_nonneg (by norm_num) n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hos
  have hsum n t := linear_sum_congr_on_prefix (fun j => τ n j ω) (hτm n ω)
    (fun t => A t ω) (fun t => A t ω) Hs (fun t => H t ω) (realTimeClamp (c k)) t
    (fun _ _ => rfl) (fun s hs => congrArg (fun t => H t ω) (min_eq_right hs))
  have hint (t : ClosedTime T) : signedIntegralRaw (α.toSignedMeasure-β.toSignedMeasure)
      ((Iic (finitePrefixTime (c k) (hc k) t).val).indicator (fun r => Hs (realTimeClamp r))) =
      I (min (realTimeClamp (c k)) t) ω := by
    rw [hmeasure,hfω t]
    apply signedIntegralRaw_congr_ae (ξ ω).totalVariation (ξ ω) 1 (by norm_num) (by simp)
    filter_upwards [hsω] with r hr
    by_cases ht : r ∈ Iic (finitePrefixTime (c k) (hc k) t).val
    · simp only [indicator_of_mem ht,Hs,min_eq_right (real_time_clamp_mono hr.2)]
    · simp only [indicator_of_notMem ht]
  convert hlim using 1
  · funext n t
    exact (hsum n t).symm
  · funext t
    exact (hint t).symm

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.variation_integral_approximation
