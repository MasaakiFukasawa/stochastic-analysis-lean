import Chapter8GibbsIntegrability
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open MeasureTheory
namespace Asakura.Chapter8

/-- The nonconvex cosine example has exactly the C3 regularity and bounded
second and third derivatives required in the Gibbs theorem. -/
theorem cosine_potential_derivatives (c : ℝ) :
    ContDiff ℝ 3 (fun x : ℝ => x^2/2+c*Real.cos x) ∧
    (∀ x, HasDerivAt (fun x : ℝ => x^2/2+c*Real.cos x) (x-c*Real.sin x) x) ∧
    (∀ x, HasDerivAt (fun x : ℝ => x-c*Real.sin x) (1-c*Real.cos x) x) ∧
    (∀ x, HasDerivAt (fun x : ℝ => 1-c*Real.cos x) (c*Real.sin x) x) ∧
    (∀ x, |1-c*Real.cos x|≤1+|c|) ∧ (∀ x, |c*Real.sin x|≤|c|) := by
  refine ⟨by fun_prop,?_,?_,?_,?_,?_⟩
  · intro x
    convert (((hasDerivAt_id x).pow 2).div_const 2).add ((Real.hasDerivAt_cos x).const_mul c) using 1
    · rfl
    · simp only [id_eq,pow_one]; ring
  · intro x
    exact (hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).const_mul c)
  · intro x
    convert (hasDerivAt_const x (1:ℝ)).sub ((Real.hasDerivAt_cos x).const_mul c) using 1 <;> ring
  · intro x
    have hc : |c*Real.cos x|≤|c| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg c)).trans_eq (mul_one _)
    calc
      _ ≤ |(1:ℝ)|+|c*Real.cos x| := abs_sub _ _
      _ ≤ 1+|c| := by rw [abs_one]; exact add_le_add le_rfl hc
  · intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) (abs_nonneg c)).trans_eq (mul_one _)

theorem cosine_potential_negative_curvature (c : ℝ) (hc : 1<c) :
    deriv (fun x : ℝ => x-c*Real.sin x) 0<0 := by
  rw [(cosine_potential_derivatives c).2.2.1 0 |>.deriv]
  simpa using sub_neg.mpr hc

theorem cosine_potential_not_convex (c : ℝ) (hc : 1<c) :
    ¬ConvexOn ℝ Set.univ (fun x : ℝ => x^2/2+c*Real.cos x) := by
  intro h
  have hd := (cosine_potential_derivatives c).2.1
  have hm := h.monotoneOn_deriv (fun x _ => (hd x).differentiableAt)
  have hg : Monotone (fun x : ℝ => x-c*Real.sin x) := by
    intro x y hxy
    have hh := hm (Set.mem_univ x) (Set.mem_univ y) hxy
    simpa only [(hd x).deriv, (hd y).deriv] using hh
  exact (not_lt_of_ge (hg.deriv_nonneg (x := 0)))
    (cosine_potential_negative_curvature c hc)

end Asakura.Chapter8
