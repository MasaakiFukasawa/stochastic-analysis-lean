import Chapter3QuadraticVariationRegularity
import Chapter2LocalQuadraticVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Localized quadratic approximation for an actual bounded continuous
adapted weight. Stopping-value measurability, essential boundedness, and
quadratic-variation regularity are consequences, not hypotheses. The
Stieltjes measure is built pathwise outside the derived common null set. -/
theorem bounded_continuous_quadratic_approximation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (hHm : ∀ t, Measurable[F t] (H t))
    (hHc : ∀ ω, Continuous (fun t => H t ω))
    (hHb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hiQ : Integrable (Q (realTimeClamp d)) P)
    (hHosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n) :
    ∀ᵐ ω ∂P,
      ∃ (hQm : MonotoneOn (fun r => Q (realTimeClamp r) ω) (Icc 0 d))
        (hQr : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r) ω) (Icc 0 d ∩ Ici x) x),
      let μ := (intervalStieltjes 0 d hd (fun r => Q (realTimeClamp r) ω) hQm hQr).measure
      TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω *
        (X (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-
          X (min (τ n j ω) (min (realTimeClamp d) t)) ω)^2)
      (fun t => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ω ∂μ) atTop := by
  have hw n j := continuous_adapted_stopping_weights P F hF hle H hHm hHc (τ n j) (hτ n j) K hHb
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨hc,he⟩ := actual_discrete_qv_error_ae_uniform P F hF hle hnull X Q hX hQ τ
    hτ hτmono hτtop hτ0 hcofinal K hK hb (fun n j ω => H (τ n j ω) ω)
    (fun n j => (hw n j).1) (fun n j => (hw n j).2.1) (fun n j => (hw n j).2.2) (realTimeClamp d) hdt hiQ
  filter_upwards [he,hHosc,local_quadratic_variation_monotone P F hF hle hnull X Q hX hQ] with ω heω hoscω hmono
  have hrt (r : ℝ) (hr : r ∈ Icc (0:ℝ) d) : realTimeClamp (T := T) r < ⊤ := by
    change (realTimeClamp r : EReal) < T
    rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
    exact (EReal.coe_le_coe hr.2).trans_lt hdT
  have hQm : MonotoneOn (fun r => Q (realTimeClamp r) ω) (Icc 0 d) :=
    fun a ha b hb hab => hmono (hrt a ha) (hrt b hb) (real_time_clamp_mono hab)
  have hQr : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r) ω) (Icc 0 d ∩ Ici x) x :=
    fun x hx => (covariance_real_continuous_on P F X X Q hX hX hQ d hdT ω x hx).mono inter_subset_left
  refine ⟨hQm,hQr,?_⟩
  let μ := (intervalStieltjes 0 d hd (fun r => Q (realTimeClamp r) ω) hQm hQr).measure
  have hr := stopped_stieltjes_uniform_approximation d hd hdT (fun t => Q t ω)
    (fun t => H t ω) hQm hQr ((hHc ω).comp real_time_clamp_continuous).measurable (fun n j => τ n j ω)
    (fun n => hτmono n ω) (fun n => hτ0 n ω) (fun n => hcofinal n ω)
    (fun n => (1/2:ℝ)^n) (fun n => pow_nonneg (by norm_num) n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hoscω
  have hl := uniform_limit_of_continuous_path_error
    (fun n => continuousPath
      (fun t ω => ∑' j, H (τ n j ω) ω*partitionDefect X Q (τ n) j (min (realTimeClamp d) t) ω)
      (hc n) ω)
    (fun n t => ∑' j, H (τ n j ω) ω*(Q (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-
      Q (min (τ n j ω) (min (realTimeClamp d) t)) ω))
    (fun t => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ω ∂μ)
    heω hr
  have heq : (fun n t => ∑' j, H (τ n j ω) ω *
        (X (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-
          X (min (τ n j ω) (min (realTimeClamp d) t)) ω)^2) =
      (fun n t => continuousPath
        (fun t ω => ∑' j, H (τ n j ω) ω*partitionDefect X Q (τ n) j (min (realTimeClamp d) t) ω)
        (hc n) ω t +
        ∑' j, H (τ n j ω) ω*(Q (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-
          Q (min (τ n j ω) (min (realTimeClamp d) t)) ω)) := by
    funext n t
    exact partition_quadratic_sum_decomposition (fun j => τ n j ω) (hτmono n ω)
      (hcofinal n ω) (fun t => X t ω) (fun t => Q t ω) (fun j => H (τ n j ω) ω)
      (realTimeClamp d) (min (realTimeClamp d) t) hdt (min_le_left _ _)
  rw [heq]
  exact hl

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bounded_continuous_quadratic_approximation
