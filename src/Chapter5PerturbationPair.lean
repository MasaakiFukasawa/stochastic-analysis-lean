import Chapter5Perturbation

open Filter Asymptotics
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- The two printed component estimates give the recurrence for their
sum, with constants independent of epsilon, and hence each component's
claimed order. -/
theorem perturbation_pair_bigO
    (Y Z : ℕ → ℝ → ℝ) (a b C D r : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 < r)
    (hY : ∀ n e,0 ≤ Y n e) (hZ : ∀ n e,0 ≤ Z n e)
    (hbaseY : ∀ e,|e| ≤ r → Y 0 e ≤ a*D*|e|)
    (hbaseZ : ∀ e,|e| ≤ r → Z 0 e ≤ b*D*|e|)
    (hstepY : ∀ n e,|e| ≤ r → Y (n+1) e ≤ a*C*|e| *(Y n e+Z n e))
    (hstepZ : ∀ n e,|e| ≤ r → Z (n+1) e ≤ b*C*|e| *(Y n e+Z n e)) :
    (∀ n e,|e| ≤ r → Y n e+Z n e ≤ ((a+b)*D)*((a+b)*C)^n*|e|^(n+1)) ∧
    (∀ n,(Y n) =O[𝓝 0] (fun e : ℝ => |e|^(n+1)) ∧
      (Z n) =O[𝓝 0] (fun e : ℝ => |e|^(n+1))) := by
  let E := fun n e => Y n e+Z n e
  have hbase e (he : |e| ≤ r) : |E 0 e| ≤ ((a+b)*D)*|e| := by
    rw [abs_of_nonneg (add_nonneg (hY 0 e) (hZ 0 e))]
    nlinarith [hbaseY e he,hbaseZ e he]
  have hstep n e (he : |e| ≤ r) : |E (n+1) e| ≤ ((a+b)*C)*|e| * |E n e| := by
    rw [abs_of_nonneg (add_nonneg (hY (n+1) e) (hZ (n+1) e)),abs_of_nonneg (add_nonneg (hY n e) (hZ n e))]
    nlinarith [hstepY n e he,hstepZ n e he]
  have hsum n e (he : |e| ≤ r) : Y n e+Z n e ≤ ((a+b)*D)*((a+b)*C)^n*|e|^(n+1) := by
    have hh := perturbation_error_bound E ((a+b)*D) ((a+b)*C) r (by positivity) (by positivity) hbase hstep n e he
    simpa only [E,abs_of_nonneg (add_nonneg (hY n e) (hZ n e))] using hh
  refine ⟨hsum,?_⟩
  intro n
  have hsmall : ∀ᶠ e : ℝ in 𝓝 0,|e| ≤ r := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with e he
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using he : |e| < r).le
  constructor
  · apply IsBigO.of_bound (((a+b)*D)*((a+b)*C)^n)
    filter_upwards [hsmall] with e he
    simp only [Real.norm_eq_abs,abs_of_nonneg (hY n e),abs_pow,abs_abs]
    exact (le_add_of_nonneg_right (hZ n e)).trans (hsum n e he)
  · apply IsBigO.of_bound (((a+b)*D)*((a+b)*C)^n)
    filter_upwards [hsmall] with e he
    simp only [Real.norm_eq_abs,abs_of_nonneg (hZ n e),abs_pow,abs_abs]
    exact (le_add_of_nonneg_left (hY n e)).trans (hsum n e he)

end Asakura.Chapter5
