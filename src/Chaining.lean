import Appendix
open Set Filter
open scoped Topology BigOperators
namespace Asakura

/-- C.2: finite two-sided chaining. All indices and the scale-zero term are explicit. -/
theorem finite_two_sided_chaining {E : Type*} [PseudoMetricSpace E]
    (u v : ℕ → E) (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hbase : dist (u 0) (v 0) ≤ K 0)
    (hu : ∀ i, dist (u (i+1)) (u i) ≤ K (i+1))
    (hv : ∀ i, dist (v (i+1)) (v i) ≤ K (i+1)) :
    ∀ n, dist (u n) (v n) ≤ 2 * ∑ i ∈ Finset.range (n+1), K i := by
  intro n
  induction n with
  | zero => simpa using hbase.trans (by linarith [hK 0] : K 0 ≤ 2 * K 0)
  | succ n ih =>
    have htri := dist_triangle (u (n+1)) (u n) (v (n+1))
    have htri' := dist_triangle (u n) (v n) (v (n+1))
    have hu' := hu n
    have hv' := hv n
    rw [dist_comm (v (n+1)) (v n)] at hv'
    rw [Finset.sum_range_succ]
    linarith

/-- C.2: chaining from eventually fixed grid approximations to the infinite tail. -/
theorem infinite_two_sided_chaining {E : Type*} [PseudoMetricSpace E]
    (u v : ℕ → E) (s t : E) (K : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hsum : Summable K)
    (hbase : dist (u 0) (v 0) ≤ K 0)
    (hu : ∀ i, dist (u (i+1)) (u i) ≤ K (i+1))
    (hv : ∀ i, dist (v (i+1)) (v i) ≤ K (i+1))
    (hs : ∀ᶠ n in atTop, u n = s) (ht : ∀ᶠ n in atTop, v n = t) :
    dist s t ≤ 2 * ∑' i, K i := by
  obtain ⟨n, hn, hn'⟩ := (hs.and ht).exists
  rw [← hn, ← hn']
  exact (finite_two_sided_chaining u v K hK hbase hu hv n).trans
    (mul_le_mul_of_nonneg_left (hsum.sum_le_tsum (Finset.range (n+1))
      (fun i _ => hK i)) (by norm_num))

/-- The weighted tail is controlled by the full weighted series, without
silently assigning a value to a divergent real-valued tsum. -/
theorem weighted_tail_bound (K w : ℕ → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hw : ∀ i, 0 ≤ w i) (hwmono : Monotone w)
    (hsum : Summable (fun i => w i * K i)) (m : ℕ) :
    ∑' i, w m * K (m+i) ≤ ∑' i, w i * K i := by
  have hmajor : Summable (fun i => w (m+i) * K (m+i)) :=
    hsum.comp_injective (fun i j h => Nat.add_left_cancel h)
  have hminor : Summable (fun i => w m * K (m+i)) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw m) (hK _))
      (fun i => mul_le_mul_of_nonneg_right (hwmono (Nat.le_add_right m i)) (hK _)) hmajor
  apply (Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_right
    (hwmono (Nat.le_add_right m i)) (hK _)) hminor hmajor).trans
  exact Summable.tsum_le_tsum_of_inj (fun i => m+i) (fun i j h => Nat.add_left_cancel h)
    (fun i _ => mul_nonneg (hw i) (hK i)) (fun i => le_rfl) hmajor hsum
end Asakura
