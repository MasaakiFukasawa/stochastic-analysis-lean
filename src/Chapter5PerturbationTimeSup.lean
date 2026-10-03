import Chapter5PerturbationPair

open Filter Asymptotics Set
open scoped Topology
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

/-- A uniform nonnegative bound gives the actual supremum's big-O bound;
no boundedness of that supremum is left implicit. -/
theorem nonnegative_sup_bigO {ι : Type*} [Nonempty ι]
    (F : ι → ℝ → ℝ) (C r : ℝ) (hr : 0 < r) (k : ℕ)
    (hF0 : ∀ i e,0 ≤ F i e)
    (hb : ∀ e,|e| ≤ r → ∀ i,F i e ≤ C*|e|^k) :
    (fun e => ⨆ i,F i e) =O[𝓝 0] (fun e : ℝ => |e|^k) := by
  classical
  apply IsBigO.of_bound C
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with e he
  have he' : |e| ≤ r := (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using he : |e| < r).le
  have hbd : BddAbove (range (fun i => F i e)) := ⟨C*|e|^k,fun x hx => by obtain ⟨i,rfl⟩ := hx;exact hb e he' i⟩
  have hnonneg : 0 ≤ ⨆ i,F i e := (hF0 (Classical.choice inferInstance) e).trans (le_ciSup hbd _)
  simp only [Real.norm_eq_abs,abs_of_nonneg hnonneg,abs_pow,abs_abs]
  exact ciSup_le (hb e he')

/-- The final time-uniform error claim follows from the same energy
estimate and the already proved recurrence for the Y and Z errors. -/
theorem perturbation_time_sup_bigO {ι : Type*} [Nonempty ι]
    (E : ℕ → ℝ → ℝ) (U : ℕ → ℝ → ι → ℝ)
    (A K c C D r : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 < r)
    (hE : ∀ n e,|e| ≤ r → E n e ≤ A*K^n*|e|^(n+1))
    (hU0 : ∀ n e t,0 ≤ U n e t)
    (hbase : ∀ e,|e| ≤ r → ∀ t,U 0 e t ≤ c*D*|e|)
    (hstep : ∀ n e,|e| ≤ r → ∀ t,U (n+1) e t ≤ c*C*|e| *E n e) :
    ∀ n,(fun e => ⨆ t,U n e t) =O[𝓝 0] (fun e : ℝ => |e|^(n+1)) := by
  intro n
  cases n with
  | zero =>
    apply nonnegative_sup_bigO (fun t e => U 0 e t) (c*D) r hr 1 (fun t e => hU0 0 e t)
    intro e he t
    simpa only [pow_one] using hbase e he t
  | succ n =>
    apply nonnegative_sup_bigO (fun t e => U (n+1) e t) (c*C*A*K^n) r hr (n+1+1)
      (fun t e => hU0 (n+1) e t)
    intro e he t
    calc
      U (n+1) e t ≤ c*C*|e| *E n e := hstep n e he t
      _ ≤ c*C*|e| *(A*K^n*|e|^(n+1)) := mul_le_mul_of_nonneg_left (hE n e he) (by positivity)
      _ = (c*C*A*K^n)*|e|^(n+1+1) := by ring

end Asakura.Chapter5
