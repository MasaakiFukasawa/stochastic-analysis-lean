import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Metric
open scoped ContDiff Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- A bounded continuous function admits smooth approximations with one
common bound. This is applied to the derivative in the C1 chain rule. -/
theorem bounded_continuous_smooth_approximation (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n x, |g n x| ≤ 3*C) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
  choose g hg happrox using fun n : ℕ =>
    hf.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
      (by positivity : 0 < (1:ℝ)/(n+1))
  refine ⟨g,hg,?_,?_⟩
  · intro n x
    have hd : dist (g n x) (f x) ≤ 2*C := happrox n x (2*C) (fun y _ => by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hb y,hb x]))
    calc
      |g n x| ≤ |g n x-f x|+|f x| := by
        simpa only [sub_add_cancel] using abs_add_le (g n x-f x) (f x)
      _ ≤ 3*C := by rw [Real.dist_eq] at hd; linarith [hb x]
  · intro x
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := x)) (ε/2) (by linarith)
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      ((tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0)).eventually (gt_mem_nhds hδ))
    refine ⟨N,fun n hn => ?_⟩
    have hbound : dist (g n x) (f x) ≤ ε/2 := happrox n x (ε/2) (fun y hy =>
      (hd ((mem_ball.mp hy).trans (hN n hn))).le)
    linarith

/-- Cutting off those approximations gives compact support without losing
the common bound or pointwise convergence. -/
theorem bounded_continuous_compact_smooth_approximation (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ HasCompactSupport (g n)) ∧
      (∀ n x, |g n x| ≤ 3*C) ∧ ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
  obtain ⟨g,hg,hbound,ht⟩ := bounded_continuous_smooth_approximation f hf C hC hb
  let φ : ℕ → ContDiffBump (0:ℝ) := fun n => ⟨n+1,2*(n+1),by positivity,by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith⟩
  refine ⟨fun n x => φ n x*g n x,fun n => ⟨(φ n).contDiff.mul (hg n),
    (φ n).hasCompactSupport.mul_right⟩,?_,?_⟩
  · intro n x
    rw [abs_mul,abs_of_nonneg (φ n).nonneg]
    exact (mul_le_mul_of_nonneg_right (φ n).le_one (abs_nonneg _)).trans (by simpa using hbound n x)
  · intro x
    have he : ∀ᶠ n : ℕ in atTop, φ n x = 1 := by
      obtain ⟨N,hN⟩ := exists_nat_gt |x|
      filter_upwards [eventually_ge_atTop N] with n hn
      apply (φ n).one_of_mem_closedBall
      change dist x 0 ≤ (n:ℝ)+1
      rw [Real.dist_eq,sub_zero]
      exact hN.le.trans (by exact_mod_cast (show N ≤ n+1 by omega))
    have hφ : Tendsto (fun n => φ n x) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
    simpa only [one_mul] using hφ.mul (ht x)

end Asakura.Chapter12
