import Chapter9GaussianDomination
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem power_one_add_sq_bound (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (1+r^2)^n ≤ (2:ℝ)^n*(1+r^(2*n)) := by
  by_cases h : r ≤ 1
  · have h1 : 1+r^2 ≤ 2 := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+r^2) h1 n
    have ht : (2:ℝ)^n ≤ (2:ℝ)^n*(1+r^(2*n)) := by
      nlinarith [pow_nonneg hr (2*n),pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
    exact hp.trans ht
  · have h1 : 1+r^2 ≤ 2*r^2 := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+r^2) h1 n
    rw [mul_pow,←pow_mul] at hp
    have ht : (2:ℝ)^n*r^(2*n) ≤ (2:ℝ)^n*(1+r^(2*n)) := by
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
    exact hp.trans ht

theorem norm_iterated_exp (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp x‖=Real.exp x := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,Real.iter_deriv_exp,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos x)]

/-- Every derivative of the exponential of a quadratic-growth exponent
is dominated uniformly when its Gaussian tail is retained. This formalizes
the all-order polynomial-times-Gaussian estimate used in the manuscript. -/
theorem exponential_quadratic_all_order_bound {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U S : Set E) (hU : IsOpen U) (hSU : S ⊆ U) (q : X → E → ℝ) (r : X → ℝ)
    (hr : ∀ x,0 ≤ r x) (n : ℕ) (K A c : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hc : 0<c)
    (hq : ∀ x,ContDiffOn ℝ ∞ (q x) U)
    (hder : ∀ x y,y∈S → ∀ i,1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (q x) U y‖ ≤ K*(1+(r x)^2))
    (htail : ∀ x y,y∈S → Real.exp (q x y) ≤ A*Real.exp (-c*(r x)^2)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ x y,y∈S →
      ‖iteratedFDerivWithin ℝ n (fun z => Real.exp (q x z)) U y‖ ≤ B := by
  obtain ⟨C,hC,hpoly⟩ := polynomial_gaussian_bound c hc (2*n)
  refine ⟨(n.factorial:ℝ)*A*(1+K)^n*2^n*C,by positivity,?_⟩
  intro x y hy
  let D := 1+K*(1+(r x)^2)
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have hh : 0 ≤ K*(1+(r x)^2) := by positivity
    linarith
  have hd i (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (q x) U y‖ ≤ D^i :=
    (hder x y hy i hi hin).trans ((show K*(1+(r x)^2) ≤ D by dsimp [D]; linarith).trans
      (le_self_pow₀ hD1 (by omega)))
  have he i (_ : i ≤ n) : ‖iteratedFDerivWithin ℝ i Real.exp univ (q x y)‖ ≤ Real.exp (q x y) := by
    rw [iteratedFDerivWithin_univ,norm_iterated_exp]
  have hb := norm_iteratedFDerivWithin_comp_le
    (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ ∞ Real.exp univ)
    (hq x) (show (n:WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)
    uniqueDiffOn_univ hU.uniqueDiffOn (fun _ _ => mem_univ _) (hSU hy) he hd
  have hD : D ≤ (1+K)*(1+(r x)^2) := by dsimp [D]; nlinarith [sq_nonneg (r x)]
  have hp := pow_le_pow_left₀ (zero_le_one.trans hD1) hD n
  rw [mul_pow] at hp
  have hp' : D^n ≤ (1+K)^n*2^n*(1+(r x)^(2*n)) := by
    have hh := mul_le_mul_of_nonneg_left (power_one_add_sq_bound (r x) (hr x) n)
      (show 0 ≤ (1+K)^n by positivity)
    exact hp.trans (by simpa only [mul_assoc] using hh)
  have hn : 0 ≤ (n.factorial:ℝ) := by positivity
  calc
    _  ≤  (n.factorial:ℝ)*Real.exp (q x y)*D^n := hb
    _  ≤  (n.factorial:ℝ)*(A*Real.exp (-c*(r x)^2))*
        ((1+K)^n*2^n*(1+(r x)^(2*n))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (htail x y hy) hn) hp'
        (by positivity) (by positivity)
    _ = ((n.factorial:ℝ)*A*(1+K)^n*2^n)*
        ((1+(r x)^(2*n))*Real.exp (-c*(r x)^2)) := by ring
    _  ≤  _ := mul_le_mul_of_nonneg_left (hpoly (r x) (hr x)) (by positivity)
end Asakura.Chapter9
