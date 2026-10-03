import FullAuditChapter4Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.Completeness

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4

/-- The square roots of the printed factorial bounds are summable, not merely
convergent to zero. This is the step needed to sum the Picard increments. -/
theorem summable_sqrt_factorial (a : ℝ) (ha : 0 ≤ a) :
    Summable (fun n : ℕ => Real.sqrt (a^n / (n.factorial : ℝ))) := by
  let f := fun n : ℕ => Real.sqrt (a^n / (n.factorial : ℝ))
  have hf n : 0 ≤ f n := Real.sqrt_nonneg _
  have hs n : (f n)^2 = a^n / (n.factorial : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hrec (n : ℕ) : ((n:ℝ)+1) * (f (n+1))^2 = a * (f n)^2 := by
    rw [hs, hs, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n.factorial:ℝ) ≠ 0 := by positivity
    have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  apply summable_of_ratio_norm_eventually_le (r := (1/2:ℝ)) (by norm_num)
  obtain ⟨N,hN⟩ := exists_nat_gt (4*a)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hlarge : 4*a ≤ (n:ℝ)+1 := by
    have hnn : (N:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf _), abs_of_nonneg (hf _)]
  have hrec' := hrec n
  have hsq := mul_nonneg (sub_nonneg.mpr hlarge) (sq_nonneg (f (n+1)))
  by_cases hzero : a = 0
  · have hz : f (n+1) = 0 := by simp [f,hzero]
    rw [hz]; positivity
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hsquares : 4*(f (n+1))^2 ≤ (f n)^2 := by
      apply (mul_le_mul_iff_left₀ hapos).mp
      nlinarith
    nlinarith [hf n, hf (n+1)]

/-- Exact iteration of the Volterra estimate. Stochastic estimates producing
u and the constant A are separate obligations, not assumed verified here. -/
theorem picard_factorial_bound (u : ℕ → ℝ → ℝ) (A c T : ℝ)
    (hc : 0 ≤ c) (hu : ∀ n, Continuous (u n))
    (hbase : ∀ t ∈ Icc 0 T, u 0 t ≤ A)
    (hstep : ∀ n t, t ∈ Icc 0 T → u (n+1) t ≤ c * ∫ s in 0..t, u n s) :
    ∀ n t, t ∈ Icc 0 T → u n t ≤ A*c^n*t^n/(n.factorial:ℝ) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    intro t ht
    have hi := intervalIntegral.integral_mono_on (μ := volume) ht.1 ((hu n).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (fun s : ℝ => A*c^n*s^n/(n.factorial:ℝ))).intervalIntegrable 0 t)
      (fun s hs => ih s ⟨hs.1,hs.2.trans ht.2⟩)
    calc
      u (n+1) t ≤ c * ∫ s in 0..t, u n s := hstep n t ht
      _ ≤ c * ∫ s in 0..t, A*c^n*s^n/(n.factorial:ℝ) := mul_le_mul_of_nonneg_left hi hc
      _ = A*c^(n+1)*t^(n+1)/((n+1).factorial:ℝ) := by
        simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp
        <;> ring

/-- Summability of the norm bounds yields an actual limit in the complete
space, and continuity of the Picard map identifies its fixed point. -/
theorem picard_fixed_point {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (Φ : E → E) (hΦ : Continuous Φ) (X : ℕ → E) (hiter : ∀ n, X (n+1) = Φ (X n))
    (A a : ℝ) (ha : 0 ≤ a)
    (hbound : ∀ n, ‖X (n+1)-X n‖ ≤ A * Real.sqrt (a^n/(n.factorial:ℝ))) :
    ∃ x, Tendsto X atTop (𝓝 x) ∧ Φ x = x := by
  have hsum : Summable (fun n => ‖X (n+1)-X n‖) :=
    ((summable_sqrt_factorial a ha).mul_left A).of_nonneg_of_le
      (fun n => norm_nonneg _) hbound
  have hd : Summable (fun n => dist (X n) (X (n+1))) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hsum
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hd)
  refine ⟨x,hx,?_⟩
  have hshift : Tendsto (fun n => X (n+1)) atTop (𝓝 x) := hx.comp (tendsto_add_atTop_nat 1)
  have hmap := hΦ.continuousAt.tendsto.comp hx
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, ← hiter] using hmap) hshift

end Asakura.Chapter4
