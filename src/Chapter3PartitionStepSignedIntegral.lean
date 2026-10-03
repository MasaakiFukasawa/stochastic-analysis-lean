import Chapter3PartitionStepPaths
import Chapter3StoppedPartitionCoordinates
import Chapter2SignedElementaryIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- A finite Ioc step integral needs no absence-of-atoms hypothesis. -/
theorem signed_integral_finite_Ioc_steps
    {ι : Type*} (ν : SignedMeasure ℝ) (s : Finset ι) (a b G : ι → ℝ) :
    signedIntegralRaw ν (fun r => ∑ i ∈ s, (Ioc (a i) (b i)).indicator (fun _ => G i) r) =
      ∑ i ∈ s, G i*ν (Ioc (a i) (b i)) := by
  classical
  unfold signedIntegralRaw
  rw [integral_finset_sum,integral_finset_sum,← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator measurableSet_Ioc,integral_indicator measurableSet_Ioc,
      setIntegral_const,setIntegral_const,ν.apply_eq_posPart_real_sub_negPart_real measurableSet_Ioc]
    simp only [smul_eq_mul]
    ring
  all_goals intro i hi; exact (integrable_const _).indicator measurableSet_Ioc

/-- Cutting a partition at the integration horizon preserves its step
function on the support of the Stieltjes measure. -/
theorem partition_step_cut_real
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (H : ClosedTime T → ℝ) (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (N : ℕ) (hN : realTimeClamp d ≤ τ N)
    (r : ℝ) (hr : r ∈ Ioc 0 d) :
    partitionStep H τ (realTimeClamp r) =
      ∑ j ∈ Finset.range N,
        (Ioc (finitePrefixTime d hd (τ j)).val (finitePrefixTime d hd (τ (j+1))).val).indicator
          (fun _ => H (τ j)) r := by
  have hrT : (r:EReal) ≤ T := (EReal.coe_le_coe hr.2).trans hdT
  have hrd : realTimeClamp (T := T) r ≤ realTimeClamp d := real_time_clamp_mono hr.2
  have hmem (j) : r ∈ Ioc (finitePrefixTime d hd (τ j)).val (finitePrefixTime d hd (τ (j+1))).val ↔
      realTimeClamp r ∈ Ioc (τ j) (τ (j+1)) := by
    have hc (i) := finite_prefix_time_clamp (T := T) d hd hdT (τ i)
    have hle (i) : r ≤ (finitePrefixTime d hd (τ i)).val ↔ realTimeClamp r ≤ min (realTimeClamp d) (τ i) := by
      rw [← hc i]
      change r ≤ _ ↔ (realTimeClamp r : EReal) ≤ (realTimeClamp _ : EReal)
      rw [real_time_clamp_eq r hr.1.le hrT,
        real_time_clamp_eq _ (finitePrefixTime d hd (τ i)).property.1
          ((EReal.coe_le_coe (finitePrefixTime d hd (τ i)).property.2).trans hdT)]
      exact EReal.coe_le_coe_iff.symm
    have hlt (i) : (finitePrefixTime d hd (τ i)).val < r ↔ min (realTimeClamp d) (τ i) < realTimeClamp r := by
      simpa only [not_le] using not_congr (hle i)
    simp only [mem_Ioc,hlt,hle,min_lt_iff,le_min_iff,not_lt_of_ge hrd,false_or,true_and,hrd]
  unfold partitionStep
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Set.indicator,hmem]
  · intro j hj
    apply indicator_of_notMem
    intro hm
    have hNj : N ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    exact not_lt_of_ge (hrd.trans (hN.trans (hτ hNj))) hm.1

/-- The actual countable step integrand has the expected signed integral.
Its finite representation is derived from the partition and measure support. -/
theorem partition_step_signed_integral
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (H : ClosedTime T → ℝ) (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (N : ℕ) (hN : realTimeClamp d ≤ τ N) (ν : SignedMeasure ℝ)
    (hsupp : ∀ᵐ r ∂ν.totalVariation, r ∈ Ioc 0 d) :
    signedIntegralRaw ν (fun r => partitionStep H τ (realTimeClamp r)) =
      ∑ j ∈ Finset.range N, H (τ j)*ν (Ioc (finitePrefixTime d hd (τ j)).val
        (finitePrefixTime d hd (τ (j+1))).val) := by
  have he := hsupp.mono (fun r hr => partition_step_cut_real d hd hdT H τ hτ N hN r hr)
  rw [signedIntegralRaw_congr_ae ν.totalVariation ν 1 (by norm_num) (by simp) he]
  exact signed_integral_finite_Ioc_steps ν (Finset.range N) _ _ _

/-- Local finiteness also supplies absolute integrability of the step
function for every finite signed measure supported on the prefix. -/
theorem partition_step_signed_integrable
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) ≤ T)
    (H : ClosedTime T → ℝ) (τ : ℕ → ClosedTime T) (hτ : Monotone τ)
    (N : ℕ) (hN : realTimeClamp d ≤ τ N) (ν : SignedMeasure ℝ)
    (hsupp : ∀ᵐ r ∂ν.totalVariation, r ∈ Ioc 0 d) :
    Integrable (fun r => partitionStep H τ (realTimeClamp r)) ν.totalVariation := by
  have he := hsupp.mono (fun r hr => partition_step_cut_real d hd hdT H τ hτ N hN r hr)
  have hi : Integrable (fun r => ∑ j ∈ Finset.range N,
      (Ioc (finitePrefixTime d hd (τ j)).val (finitePrefixTime d hd (τ (j+1))).val).indicator
        (fun _ => H (τ j)) r) ν.totalVariation := by
    apply integrable_finset_sum
    intro j hj
    exact (integrable_const _).indicator measurableSet_Ioc
  exact hi.congr (he.mono (fun _ h => h.symm))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.signed_integral_finite_Ioc_steps
#print axioms Asakura.Chapter3Complete.partition_step_cut_real
#print axioms Asakura.Chapter3Complete.partition_step_signed_integral

#print axioms Asakura.Chapter3Complete.partition_step_signed_integrable
