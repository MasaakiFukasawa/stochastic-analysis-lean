import Chapter3VariationIntegralApproximation
import Chapter3CommonOscillationPartition
import Chapter3PartitionEssentialBounds
import Chapter2ItoConstructionChoices

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem increasing_partition_integral_bound
    {T : EReal} [Fact (0 ≤ T)] (A H : ClosedTime T → ℝ)
    (τ : ℕ → ClosedTime T) (hm : Monotone τ) (h0 : τ 0 = ⊥)
    (t : ClosedTime T) (N : ℕ) (hN : t ≤ τ N)
    (hA : MonotoneOn A (Iic t)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ s, s ≤ t → |H s| ≤ K) :
    |∑' j, H (τ j)*(A (min (τ (j+1)) t)-A (min (τ j) t))| ≤ K*(A t-A ⊥) := by
  rw [partition_sum_truncates_before_endpoint τ hm A (fun j => H (τ j)) N t hN]
  have hd j : 0 ≤ A (min (τ (j+1)) t)-A (min (τ j) t) :=
    sub_nonneg.mpr (hA (show min (τ j) t ∈ Iic t from min_le_right (τ j) t)
      (show min (τ (j+1)) t ∈ Iic t from min_le_right (τ (j+1)) t) (min_le_min_right t (hm (Nat.le_succ j))))
  calc
    _ ≤ ∑ j ∈ Finset.range N, |H (τ j)*(A (min (τ (j+1)) t)-A (min (τ j) t))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, K*(A (min (τ (j+1)) t)-A (min (τ j) t)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : τ j ≤ t
      · rw [abs_mul,abs_of_nonneg (hd j)]
        exact mul_le_mul_of_nonneg_right (hH _ hj) (hd j)
      · have hta := le_of_not_ge hj
        simp [min_eq_right hta,min_eq_right (hta.trans (hm (Nat.le_succ j)))]
    _ = K*(A t-A ⊥) := by
      rw [← Finset.mul_sum,Finset.sum_range_sub (fun j => A (min (τ j) t)),h0,min_eq_right hN,min_bot_left]

/-- The bounded-integrand estimate needed in both BDG integration-by-parts
arguments, for the actual variation integral on every finite prefix. -/
theorem increasing_variation_integral_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (A H I : ClosedTime T → Ω → ℝ) (hAv : AdaptedLocalVariationWitness F A)
    (hAm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (hI : VariationIntegralFormula P c hc A (fun z => H (realTimeClamp z.2) z.1) I) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → ∀ K : ℝ, 0 ≤ K →
      (∀ s, s ≤ t → |H s ω| ≤ K) → |I t ω| ≤ K*(A t ω-A ⊥ ω) := by
  obtain ⟨u,_,_,_,hum,hut,huc⟩ := positive_real_time_exhaustion hT
  obtain ⟨τ,h0,hs,hm,ht,hco,hb,_⟩ := common_oscillation_partition P F hF hle
    (fun _ : Unit => H) (fun _ => hHm) (fun _ => hHc)
    (fun n => realTimeClamp (u n)) hum.monotone hut huc
  have ho := stopped_bound_interval_oscillation P H τ (fun n => (1/2:ℝ)^n)
    (fun n j => Filter.Eventually.of_forall (fun ω t => hb () n j ω t))
  have hl k := variation_integral_approximation P F hF A H I hAv hHc c hc hcT hI τ hm h0 hco ho k
  filter_upwards [ae_all_iff.mpr hl] with ω hω
  intro t htop K hK hH
  obtain ⟨k,hk⟩ := hcc t htop
  have hlim := (hω k).tendsto_at t
  simp only [min_eq_right hk.le] at hlim
  apply le_of_tendsto hlim.abs
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨N,hN⟩ := hco n ω t htop
  exact increasing_partition_integral_bound (fun s => A s ω) (fun s => H s ω)
    (fun j => τ n j ω) (hm n ω) (h0 n ω) t N hN.le
    (fun _ hs _ ht hst => hAm ω (hs.trans_lt htop) (ht.trans_lt htop) hst) K hK hH

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.increasing_partition_integral_bound
#print axioms Asakura.Chapter3Complete.increasing_variation_integral_bound
