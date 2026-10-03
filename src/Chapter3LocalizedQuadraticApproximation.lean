import Chapter3QuadraticSumAssembly

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The localized diagonal part of the manuscript's weighted quadratic
variation approximation. Both errors are derived: the actual martingale
square-defect estimate and the actual Stieltjes measure approximation.
This statement retains explicitly the localized coefficient and partition
hypotheses; removing localization and constructing the partitions are
separate obligations. -/
theorem localized_quadratic_approximation
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
    (hA : ∀ n j, Measurable[writtenStoppedSpace m F (τ n j) (hτ n j)] (fun ω => H (τ n j ω) ω))
    (hAb : ∀ n j, MemLp (fun ω => H (τ n j ω) ω) ∞ P)
    (hAK : ∀ n j, ∀ᵐ ω ∂P, |H (τ n j ω) ω| ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (hiQ : Integrable (Q (realTimeClamp d)) P)
    (hQm : ∀ ω, MonotoneOn (fun r => Q (realTimeClamp r) ω) (Icc 0 d))
    (hQr : ∀ ω x, x ∈ Icc 0 d → ContinuousWithinAt (fun r => Q (realTimeClamp r) ω) (Icc 0 d ∩ Ici x) x)
    (hHm : ∀ ω, Measurable (fun r => H (realTimeClamp r) ω))
    (hHosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n) :
    let μ := fun ω => (intervalStieltjes 0 d hd (fun r => Q (realTimeClamp r) ω) (hQm ω) (hQr ω)).measure
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω *
        (X (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-
          X (min (τ n j ω) (min (realTimeClamp d) t)) ω)^2)
      (fun t => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ω ∂μ ω) atTop := by
  intro μ
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  obtain ⟨hc,he⟩ := actual_discrete_qv_error_ae_uniform P F hF hle hnull X Q hX hQ τ
    hτ hτmono hτtop hτ0 hcofinal K hK hb (fun n j ω => H (τ n j ω) ω)
    hA hAb hAK (realTimeClamp d) hdt hiQ
  filter_upwards [he,hHosc] with ω heω hoscω
  have hr := stopped_stieltjes_uniform_approximation d hd hdT (fun t => Q t ω)
    (fun t => H t ω) (hQm ω) (hQr ω) (hHm ω) (fun n j => τ n j ω)
    (fun n => hτmono n ω) (fun n => hτ0 n ω) (fun n => hcofinal n ω)
    (fun n => (1/2:ℝ)^n) (fun n => pow_nonneg (by norm_num) n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) hoscω
  have hl := uniform_limit_of_continuous_path_error
    (fun n => continuousPath
      (fun t ω => ∑' j, H (τ n j ω) ω*partitionDefect X Q (τ n) j (min (realTimeClamp d) t) ω)
      (hc n) ω)
    (fun n t => ∑' j, H (τ n j ω) ω*(Q (min (τ n (j+1) ω) (min (realTimeClamp d) t)) ω-
      Q (min (τ n j ω) (min (realTimeClamp d) t)) ω))
    (fun t => ∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ω ∂μ ω)
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
#print axioms Asakura.Chapter3Complete.localized_quadratic_approximation
