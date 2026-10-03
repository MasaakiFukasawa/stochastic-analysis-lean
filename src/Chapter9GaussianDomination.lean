import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Asakura.Chapter9
set_option maxHeartbeats 1200000

/-- A polynomial times a Gaussian is bounded. This quantitative bound is
uniform in the translated coordinate and works for every derivative order. -/
theorem polynomial_gaussian_bound (c : ℝ) (hc : 0<c) (n : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ r : ℝ,0≤r → (1+r^n)*Real.exp (-c*r^2)≤C := by
  let C := 2*((n.factorial:ℝ)/c^n)*Real.exp c
  have hfac : 0<(n.factorial:ℝ) := by positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro r hr
  have hbase : 1≤1+r^2 := by nlinarith [sq_nonneg r]
  have hrb : r≤1+r^2 := by nlinarith [sq_nonneg (r-1/2)]
  have hpow : 1+r^n≤2*(1+r^2)^n := by
    have h0 : (1:ℝ)≤(1+r^2)^n := one_le_pow₀ hbase
    have h1 := pow_le_pow_left₀ hr hrb n
    linarith
  have he := Real.pow_div_factorial_le_exp (c*(1+r^2)) (show 0≤c*(1+r^2) by positivity) n
  have he' : (1+r^2)^n≤((n.factorial:ℝ)/c^n)*Real.exp (c*(1+r^2)) := by
    rw [mul_pow] at he
    have hh := (div_le_iff₀ hfac).mp he
    have hh' : (1+r^2)^n≤(Real.exp (c*(1+r^2))*(n.factorial:ℝ))/c^n := by
      apply (le_div_iff₀ (pow_pos hc n)).mpr
      simpa only [mul_comm] using hh
    convert hh' using 1 <;> ring
  calc
    (1+r^n)*Real.exp (-c*r^2)≤(2*(1+r^2)^n)*Real.exp (-c*r^2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ ≤ (2*(((n.factorial:ℝ)/c^n)*Real.exp (c*(1+r^2))))*Real.exp (-c*r^2) := by
      gcongr
    _ = 2*((n.factorial:ℝ)/c^n)*(Real.exp (c*(1+r^2))*Real.exp (-c*r^2)) := by ring
    _ = C := by
      rw [←Real.exp_add,show c*(1+r^2)+ -c*r^2=c by ring]
end Asakura.Chapter9
