import Chapter3PolarizedStieltjesMeasure
import Chapter3PolarizedCovariance
import Chapter3DiscreteTruncationProbability

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Linearity of the actual infinite discrete Stieltjes sum. Local finite
support is derived from cofinality, so no unjustified tsum subtraction is used. -/
theorem linear_partition_sum_sub
    {T : EReal} [Fact (0 ≤ T)] (U V A H : ClosedTime T → ℝ)
    (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (b : ClosedTime T) (hb : b < ⊤) (hco : ∀ t, t < ⊤ → ∃ N, t < τ N)
    (he : ∀ s, s ≤ b → A s = U s-V s) (t : ClosedTime T) :
    (∑' j, H (τ j)*(A (min (τ (j+1)) (min b t))-A (min (τ j) (min b t)))) =
      (∑' j, H (τ j)*(U (min (τ (j+1)) (min b t))-U (min (τ j) (min b t))))-
      (∑' j, H (τ j)*(V (min (τ (j+1)) (min b t))-V (min (τ j) (min b t)))) := by
  obtain ⟨N,hN⟩ := hco b hb
  rw [partition_sum_truncates_before_endpoint τ hτ A (fun j => H (τ j)) N _ ((min_le_left _ _).trans hN.le),
    partition_sum_truncates_before_endpoint τ hτ U (fun j => H (τ j)) N _ ((min_le_left _ _).trans hN.le),
    partition_sum_truncates_before_endpoint τ hτ V (fun j => H (τ j)) N _ ((min_le_left _ _).trans hN.le),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he _ ((min_le_right _ _).trans (min_le_left _ _)),he _ ((min_le_right _ _).trans (min_le_left _ _))]
  ring

/-- Signed Stieltjes approximation from the positive/negative increasing
parts. The limiting signed measure and its integral are actual constructions. -/
theorem signed_stieltjes_uniform_approximation
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (U V A H : ClosedTime T → ℝ)
    (hU : MonotoneOn (fun r => U (realTimeClamp r)) (Icc 0 d))
    (hV : MonotoneOn (fun r => V (realTimeClamp r)) (Icc 0 d))
    (hrU : ∀ r, r ∈ Icc 0 d → ContinuousWithinAt (fun s => U (realTimeClamp s)) (Icc 0 d ∩ Ici r) r)
    (hrV : ∀ r, r ∈ Icc 0 d → ContinuousWithinAt (fun s => V (realTimeClamp s)) (Icc 0 d ∩ Ici r) r)
    (he : ∀ s, s ≤ realTimeClamp d → A s = U s-V s)
    (hHm : Measurable (fun r => H (realTimeClamp r)))
    (hHc : ∀ t, t < ⊤ → ContinuousAt H t)
    (τ : ℕ → ℕ → ClosedTime T) (hτ : ∀ n, Monotone (τ n)) (h0 : ∀ n, τ n 0 = ⊥)
    (hco : ∀ n t, t < ⊤ → ∃ N, t < τ n N)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hosc : ∀ n j t, τ n j ≤ t → t ≤ τ n (j+1) → |H (τ n j)-H t| ≤ δ n) :
    let α := (intervalStieltjes 0 d hd (fun r => U (realTimeClamp r)) hU hrU).measure
    let β := (intervalStieltjes 0 d hd (fun r => V (realTimeClamp r)) hV hrV).measure
    letI := intervalStieltjes_finite 0 d hd (fun r => U (realTimeClamp r)) hU hrU
    letI := intervalStieltjes_finite 0 d hd (fun r => V (realTimeClamp r)) hV hrV
    TendstoUniformly
      (fun n t => ∑' j, H (τ n j)*(A (min (τ n (j+1)) (min (realTimeClamp d) t))-
        A (min (τ n j) (min (realTimeClamp d) t))))
      (fun t => signedIntegralRaw (α.toSignedMeasure-β.toSignedMeasure)
        ((Iic (finitePrefixTime d hd t).val).indicator (fun r => H (realTimeClamp r)))) atTop := by
  intro α β
  letI := intervalStieltjes_finite 0 d hd (fun r => U (realTimeClamp r)) hU hrU
  letI := intervalStieltjes_finite 0 d hd (fun r => V (realTimeClamp r)) hV hrV
  have hu := stopped_stieltjes_uniform_approximation d hd hdT U H hU hrU hHm τ hτ h0 hco δ hδ hlim hosc
  have hv := stopped_stieltjes_uniform_approximation d hd hdT V H hV hrV hHm τ hτ h0 hco δ hδ hlim hosc
  have hiU := continuous_weight_stieltjes_integrable d hd hdT H hHc _ hU hrU
  have hiV := continuous_weight_stieltjes_integrable d hd hdT H hHc _ hV hrV
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  have heq n t := linear_partition_sum_sub U V A H (τ n) (hτ n) (realTimeClamp d) hdt (hco n) he t
  have hI (t : ClosedTime T) : signedIntegralRaw (α.toSignedMeasure-β.toSignedMeasure)
      ((Iic (finitePrefixTime d hd t).val).indicator (fun r => H (realTimeClamp r))) =
      (∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ∂α)-
      (∫ r in Iic (finitePrefixTime d hd t).val, H (realTimeClamp r) ∂β) := by
    rw [signed_difference_integral α β _ ((integrable_add_measure.mpr ⟨hiU,hiV⟩).indicator measurableSet_Iic),
      integral_indicator measurableSet_Iic,integral_indicator measurableSet_Iic]
  simp_rw [heq,hI]
  exact uniform_limit_sub _ _ _ _ hu hv

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.linear_partition_sum_sub
#print axioms Asakura.Chapter3Complete.signed_stieltjes_uniform_approximation
