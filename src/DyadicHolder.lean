import DyadicContinuity
open Filter Set
open scoped Topology
namespace Asakura

/-- C.2: the complete deterministic Holder estimate, including 2^(alpha+1). -/
theorem dyadic_holder_bound {D E : Type*} [MetricSpace D] [PseudoMetricSpace E]
    (f : D → E) (a : ℕ → D → D) (K : ℕ → ℝ)
    (α : ℝ) (hα : 0 < α) (hdiam : ∀ s t : D, dist s t ≤ 1)
    (hK : ∀ n, 0 ≤ K n)
    (hsum : Summable (fun n => (2^α : ℝ)^n * K n))
    (hfix : ∀ s, ∃ N, ∀ n ≥ N, a n s = s)
    (hstep : ∀ n s, dist (f (a (n+1) s)) (f (a n s)) ≤ K (n+1))
    (hnear : ∀ m s t, dist s t ≤ (1/2 : ℝ)^m →
      dist (f (a m s)) (f (a m t)) ≤ K m) :
    ∀ s t, dist (f s) (f t) ≤
      (2 * 2^α * ∑' n, (2^α : ℝ)^n * K n) * (dist s t)^α := by
  let q : ℝ := 2^α
  have hq : 1 ≤ q := Real.one_le_rpow (by norm_num) hα.le
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hKsum : Summable K := Summable.of_nonneg_of_le hK
    (fun n => by nlinarith [one_le_pow₀ (n := n) hq, hK n]) hsum
  have hweight : Monotone (fun n : ℕ => q^n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [pow_succ]
    nlinarith [pow_nonneg hq0 n]
  intro s t
  by_cases heq : s = t
  · subst t; simp [Real.zero_rpow hα.ne']
  obtain ⟨m, hmlo, hmhi⟩ := exists_nat_pow_near_of_lt_one
    (dist_pos.mpr heq) (hdiam s t) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have htail := dyadic_tail_estimate f a K hK hKsum hfix hstep hnear m s t hmhi
  have hwt := weighted_tail_bound K (fun n => q^n) hK
    (fun n => pow_nonneg hq0 n) hweight hsum m
  rw [tsum_mul_left] at hwt
  have htail0 : 0 ≤ ∑' i, K (m+i) := tsum_nonneg (fun i => hK _)
  have hdist0 : 0 ≤ (dist s t)^α := Real.rpow_nonneg (dist_nonneg) _
  have hpower := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(m+1)) hmlo.le hα.le
  have hinv : q^(m+1) * ((1/2:ℝ)^(m+1))^α = 1 := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    rw [mul_comm α ((m+1:ℕ):ℝ), ← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2)
      (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have hprod : 1 ≤ q^(m+1) * (dist s t)^α := by
    rw [← hinv]
    exact mul_le_mul_of_nonneg_left hpower (pow_nonneg hq0 _)
  change dist (f s) (f t) ≤ (2*q*∑' n, q^n*K n) * (dist s t)^α
  calc
    dist (f s) (f t) ≤ 2 * ∑' i, K (m+i) := htail
    _ ≤ (2 * ∑' i, K (m+i)) * (q^(m+1) * (dist s t)^α) := by
      nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) htail0]
    _ = (2*q*(q^m * ∑' i, K (m+i))) * (dist s t)^α := by rw [pow_succ]; ring
    _ ≤ (2*q*∑' n, q^n*K n) * (dist s t)^α :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwt (by positivity)) hdist0
end Asakura
