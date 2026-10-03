import Chapter3ConstructedStieltjesRiemann
import Mathlib.Topology.UniformSpace.UniformConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter2Complete
set_option maxHeartbeats 1200000

/-- A constant extension past b makes all increments beyond b vanish,
uniformly in the evaluation time. -/
theorem clamped_increment_zero_after
    (b : ℝ) (hb : 0 ≤ b) (Q : ℝ → ℝ) (a c t : ℝ) (hba : b ≤ a) (hac : a ≤ c) :
    Q (intervalClamp 0 b hb (min c t))-Q (intervalClamp 0 b hb (min a t)) = 0 := by
  have ha : intervalClamp 0 b hb a = b := by simp only [intervalClamp,projIcc_of_right_le hb hba]
  have hc : intervalClamp 0 b hb c = b := by simp only [intervalClamp,projIcc_of_right_le hb (hba.trans hac)]
  rw [(intervalClamp_mono 0 b hb).map_min,(intervalClamp_mono 0 b hb).map_min,ha,hc,sub_self]

/-- The entire infinite Stieltjes sum has the same uniform error bound.
The truncation index comes from the partition reaching the finite horizon,
and is not assumed as a finite-support property of the sum. -/
theorem constructed_stieltjes_infinite_riemann_error
    (b : ℝ) (hb : 0 ≤ b) (Q H : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc 0 b))
    (hr : ∀ x, x ∈ Icc 0 b → ContinuousWithinAt Q (Icc 0 b ∩ Ici x) x)
    (hH : Measurable H) (u : ℕ → ℝ) (hu : Monotone u) (hu0 : u 0 = 0)
    (hreach : ∃ N, b ≤ u N) (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ j x, x ∈ Ioc (u j) (u (j+1)) → |H (u j)-H x| ≤ δ) :
    let μ := (intervalStieltjes 0 b hb Q hQ hr).measure
    let Qc := fun x => Q (intervalClamp 0 b hb x)
    Integrable H μ ∧ ∀ t,
      |(∑' j, H (u j)*(Qc (min (u (j+1)) t)-Qc (min (u j) t)))-
        (∫ x in Iic t, H x ∂μ)| ≤ δ*(Q b-Q 0) := by
  intro μ Qc
  obtain ⟨N,hN⟩ := hreach
  obtain ⟨hi,he⟩ := constructed_stieltjes_riemann_error b hb Q H hQ hr hH u hu hu0 N hN δ hδ
    (fun j _ x hx => hosc j x hx)
  refine ⟨hi,?_⟩
  intro t
  have hs : (∑' j, H (u j)*(Qc (min (u (j+1)) t)-Qc (min (u j) t))) =
      ∑ j ∈ Finset.range N, H (u j)*(Qc (min (u (j+1)) t)-Qc (min (u j) t)) := by
    apply tsum_eq_sum
    intro j hj
    have hNj : N ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    rw [clamped_increment_zero_after b hb Q (u j) (u (j+1)) t (hN.trans (hu hNj))
      (hu (Nat.le_succ j)),mul_zero]
  rw [hs]
  exact he t

/-- Uniform convergence of the actual Stieltjes Riemann sums, with an
arbitrary vanishing oscillation bound (in particular the dyadic one). -/
theorem constructed_stieltjes_uniform_approximation
    (b : ℝ) (hb : 0 ≤ b) (Q H : ℝ → ℝ)
    (hQ : MonotoneOn Q (Icc 0 b))
    (hr : ∀ x, x ∈ Icc 0 b → ContinuousWithinAt Q (Icc 0 b ∩ Ici x) x)
    (hH : Measurable H) (u : ℕ → ℕ → ℝ)
    (hu : ∀ n, Monotone (u n)) (hu0 : ∀ n, u n 0 = 0)
    (hreach : ∀ n, ∃ N, b ≤ u n N) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (hosc : ∀ n j x, x ∈ Ioc (u n j) (u n (j+1)) → |H (u n j)-H x| ≤ δ n) :
    let μ := (intervalStieltjes 0 b hb Q hQ hr).measure
    let Qc := fun x => Q (intervalClamp 0 b hb x)
    TendstoUniformly (fun n t => ∑' j, H (u n j)*(Qc (min (u n (j+1)) t)-Qc (min (u n j) t)))
      (fun t => ∫ x in Iic t, H x ∂μ) atTop := by
  intro μ Qc
  have he (n) := (constructed_stieltjes_infinite_riemann_error b hb Q H hQ hr hH
    (u n) (hu n) (hu0 n) (hreach n) (δ n) (hδ n) (hosc n)).2
  have hl : Tendsto (fun n => δ n*(Q b-Q 0)) atTop (𝓝 0) := by simpa using hlim.mul_const (Q b-Q 0)
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn
  intro t
  simpa only [Real.dist_eq,abs_sub_comm] using (he n t).trans_lt hn

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.clamped_increment_zero_after
#print axioms Asakura.Chapter3Complete.constructed_stieltjes_infinite_riemann_error
#print axioms Asakura.Chapter3Complete.constructed_stieltjes_uniform_approximation
