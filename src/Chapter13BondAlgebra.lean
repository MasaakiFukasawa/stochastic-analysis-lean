import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FullAuditRatesObstructions

open scoped BigOperators
namespace Asakura.Chapter13

noncomputable def termRate (δ p q:ℝ) : ℝ := (p/q-1)/δ

theorem term_rate_positive_factor {δ p q:ℝ} (hδ:0<δ) (hp:0<p) (hq:0<q) :
    1+δ*termRate δ p q=p/q ∧ 0<1+δ*termRate δ p q := by
  have he:1+δ*termRate δ p q=p/q := by dsimp [termRate];field_simp <;> ring
  exact ⟨he,he.symm ▸ div_pos hp hq⟩

theorem term_rate_shift {δ p q:ℝ} (hδ:0<δ) :
    1/δ+termRate δ p q=(p/q)/δ := by dsimp [termRate];ring

theorem coupon_swap_equation (a z A c:ℝ) (hA:A≠0) :
    z+c*A=a ↔ c=(a-z)/A := by constructor <;> intro h <;> field_simp at * <;> nlinarith

theorem swap_payoff (a z A K:ℝ) (hA:0<A) :
    A*max ((a-z)/A-K) 0=max (a-z-K*A) 0 := by
  rw [mul_max_of_nonneg _ _ hA.le]
  congr 1
  · field_simp <;> ring
  · ring

theorem caplet_payoff {δ:ℝ} (hδ:0<δ) (p K:ℝ) :
    δ*max ((p-1)/δ-K) 0=max (p-(1+δ*K)) 0 := by
  rw [mul_max_of_nonneg _ _ hδ.le]
  congr 1
  · field_simp <;> ring
  · ring

theorem bond_ratio_telescope (p:ℕ → ℝ) (hp:∀i,p i≠0) (n:ℕ) :
    ∏i∈Finset.range n,p i/p (i+1)=p 0/p n := by
  induction n with
  | zero => simp [hp]
  | succ n ih => rw [Finset.prod_range_succ,ih];field_simp [hp]

theorem log_discounted_bond (p b:ℝ) (hp:0<p) (hb:0<b) :
    Real.log (p/b)=Real.log p-Real.log b := Real.log_div (ne_of_gt hp) (ne_of_gt hb)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.bond_ratio_telescope
