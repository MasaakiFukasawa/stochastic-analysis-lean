import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set
open scoped Topology BigOperators ContDiff
namespace Asakura.Chapter5
set_option maxHeartbeats 5000000

/-- Every derivative of exp(a f) is bounded when f and all its derivatives
are bounded. The Leibniz recurrence proves this for all orders rather
than assuming bounds on the exponential datum. -/
theorem bounded_smooth_exponential_derivatives (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (B : ℕ → ℝ)
    (hb : ∀ n x,‖iteratedDeriv n f x‖≤B n) (a : ℝ) :
    ∀ n,∃ C : ℝ,0≤C ∧ ∀ x,‖iteratedDeriv n (fun y => Real.exp (a*f y)) x‖≤C := by
  classical
  let g := fun x => a*f x
  let h := fun x => Real.exp (g x)
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul hf
  have hh : ContDiff ℝ ∞ h := hg.exp
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hde : deriv h = deriv g*h := by
    funext x
    change deriv (fun y => Real.exp (g y)) x = deriv g x*Real.exp (g x)
    simpa only [mul_comm] using ((hg.differentiable (by simp) x).hasDerivAt.exp).deriv
  have hgb (i : ℕ) (x : ℝ) : ‖iteratedDeriv i (deriv g) x‖≤|a| * B (i+1) := by
    rw [← iteratedDeriv_succ']
    dsimp only [g]
    rw [iteratedDeriv_const_mul_field,norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb (i+1) x) (abs_nonneg _)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨Real.exp (|a| * B 0),(Real.exp_pos _).le,?_⟩
      intro x
      simp only [iteratedDeriv_zero,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hb0 : |f x|≤B 0 := by simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using hb 0 x
      exact (le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left hb0 (abs_nonneg a))
    | succ n =>
      have hi : ∀ i : Fin (n+1),∃ C : ℝ,0≤C ∧ ∀ x,‖iteratedDeriv i.val h x‖≤C :=
        fun i => ih i.val i.isLt
      choose C hC hbC using hi
      let D := ∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*(|a| * B (i+1))*C ⟨n-i,by omega⟩
      have hB i : 0≤B i := (norm_nonneg (iteratedDeriv i f 0)).trans (hb i 0)
      refine ⟨D,Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (abs_nonneg a) (hB _))) (hC _)),?_⟩
      intro x
      change ‖iteratedDeriv (n+1) h x‖≤D
      rw [iteratedDeriv_succ',hde,iteratedDeriv_mul (hgd.of_le (by simp)).contDiffAt (hh.of_le (by simp)).contDiffAt]
      calc
        _ ≤ ∑ i ∈ Finset.range (n+1),‖(n.choose i:ℝ)*iteratedDeriv i (deriv g) x*iteratedDeriv (n-i) h x‖ := norm_sum_le _ _
        _ ≤ D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hgb i x) (Nat.cast_nonneg _))
            (hbC ⟨n-i,by omega⟩ x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (abs_nonneg a) (hB _)))

end Asakura.Chapter5
