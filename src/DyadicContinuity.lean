import Chaining
open Filter Set
open scoped Topology
namespace Asakura

/-- C.2: the full tail estimate for two dyadic points. The approximation is
allowed to be only eventually fixed, exactly as in the manuscript. -/
theorem dyadic_tail_estimate {D E : Type*} [MetricSpace D] [PseudoMetricSpace E]
    (f : D → E) (a : ℕ → D → D) (K : ℕ → ℝ)
    (hK : ∀ n, 0 ≤ K n) (hsum : Summable K)
    (hfix : ∀ s, ∃ N, ∀ n ≥ N, a n s = s)
    (hstep : ∀ n s, dist (f (a (n+1) s)) (f (a n s)) ≤ K (n+1))
    (hnear : ∀ m s t, dist s t ≤ (1/2 : ℝ)^m →
      dist (f (a m s)) (f (a m t)) ≤ K m)
    (m : ℕ) (s t : D) (hst : dist s t ≤ (1/2 : ℝ)^m) :
    dist (f s) (f t) ≤ 2 * ∑' i, K (m+i) := by
  apply infinite_two_sided_chaining (fun i => f (a (m+i) s))
    (fun i => f (a (m+i) t)) (f s) (f t) (fun i => K (m+i))
  · exact fun i => hK _
  · exact hsum.comp_injective (fun i j h => Nat.add_left_cancel h)
  · simpa using hnear m s t hst
  · intro i; simpa [Nat.add_assoc] using hstep (m+i) s
  · intro i; simpa [Nat.add_assoc] using hstep (m+i) t
  · obtain ⟨N, hN⟩ := hfix s
    filter_upwards [eventually_ge_atTop N] with i hi
    rw [hN (m+i) (by omega)]
  · obtain ⟨N, hN⟩ := hfix t
    filter_upwards [eventually_ge_atTop N] with i hi
    rw [hN (m+i) (by omega)]

/-- C.2: summable grid increments imply uniform continuity on the dyadic set. -/
theorem dyadic_uniform_continuity {D E : Type*} [MetricSpace D] [PseudoMetricSpace E]
    (f : D → E) (a : ℕ → D → D) (K : ℕ → ℝ)
    (hK : ∀ n, 0 ≤ K n) (hsum : Summable K)
    (hfix : ∀ s, ∃ N, ∀ n ≥ N, a n s = s)
    (hstep : ∀ n s, dist (f (a (n+1) s)) (f (a n s)) ≤ K (n+1))
    (hnear : ∀ m s t, dist s t ≤ (1/2 : ℝ)^m →
      dist (f (a m s)) (f (a m t)) ≤ K m) : UniformContinuous f := by
  have htail : Tendsto (fun m => 2 * ∑' i, K (m+i)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_sum_nat_add K)
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := (htail.eventually (gt_mem_nhds hε)).exists
  refine ⟨(1/2 : ℝ)^m, by positivity, fun s t hst => ?_⟩
  exact (dyadic_tail_estimate f a K hK hsum hfix hstep hnear m s t hst.le).trans_lt hm
end Asakura
