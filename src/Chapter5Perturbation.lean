import Mathlib.Analysis.Asymptotics.Defs
import FullAuditChapter5Estimates

open Filter Asymptotics
open scoped Topology
namespace Asakura.Chapter5

/-- Induction in the perturbation proof, with constants uniform in epsilon.
The energy inequalities producing the recurrence are separate obligations. -/
theorem perturbation_error_bound (E : ℕ → ℝ → ℝ) (A K r : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hbase : ∀ e, |e| ≤ r → |E 0 e| ≤ A*|e|)
    (hstep : ∀ n e, |e| ≤ r → |E (n+1) e| ≤ K*|e| * |E n e|) :
    ∀ n e, |e| ≤ r → |E n e| ≤ A*K^n*|e|^(n+1) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro e he
    calc
      |E (n+1) e| ≤ K*|e| * |E n e| := hstep n e he
      _ ≤ K*|e| * (A*K^n*|e|^(n+1)) :=
        mul_le_mul_of_nonneg_left (ih e he) (mul_nonneg hK (abs_nonneg e))
      _ = A*K^(n+1)*|e|^(n+1+1) := by ring

/-- Turn the explicit uniform bound into the manuscript's big-O statement. -/
theorem perturbation_bigO (E : ℕ → ℝ → ℝ) (A K r : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hr : 0 < r)
    (hbase : ∀ e, |e| ≤ r → |E 0 e| ≤ A*|e|)
    (hstep : ∀ n e, |e| ≤ r → |E (n+1) e| ≤ K*|e| * |E n e|) (n : ℕ) :
    (E n) =O[𝓝 0] (fun e : ℝ => |e|^(n+1)) := by
  apply IsBigO.of_bound (A*K^n)
  have hn : ∀ᶠ e : ℝ in 𝓝 0, |e| < r := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with e he
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using he
  filter_upwards [hn] with e he
  simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using
    perturbation_error_bound E A K r hA hK hbase hstep n e he.le

end Asakura.Chapter5
