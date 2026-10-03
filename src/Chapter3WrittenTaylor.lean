import Chapter3WrittenLimits
import Mathlib.Analysis.Calculus.Taylor

open Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter3Written

/-- The one-dimensional Taylor estimate, from C² regularity and oscillation
of the second derivative on the spatial segment, not an assumed remainder. -/
theorem taylor_second_order_oscillation {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {x y ε : ℝ} (_hε : 0 ≤ ε)
    (hosc : ∀ z ∈ uIcc x y, |iteratedDeriv 2 f z-iteratedDeriv 2 f x| ≤ ε) :
    |f y-f x-deriv f x*(y-x)-iteratedDeriv 2 f x*(y-x)^2/2| ≤ ε*(y-x)^2/2 := by
  by_cases hxy : x=y
  · subst y; simp
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxy hf.contDiffOn
  have hd : iteratedDerivWithin 1 f (uIcc x y) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (left_mem_uIcc)]
    simp
  simp only [taylorWithinEval_succ, taylor_within_zero_eval] at he
  norm_num [hd] at he
  have hr : f y-f x-deriv f x*(y-x)-iteratedDeriv 2 f x*(y-x)^2/2 =
      (iteratedDeriv 2 f z-iteratedDeriv 2 f x)*(y-x)^2/2 := by linarith
  rw [hr, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (y-x))]
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hosc z ⟨hz.1.le, hz.2.le⟩) (sq_nonneg _)) (by norm_num)

/-- In one dimension the intermediate spatial points in Taylor's theorem
are attained along the continuous path. This justifies the manuscript's
oscillation partition for f''(X). -/
theorem path_oscillation_controls_segment {X g : ℝ → ℝ} {a b ε : ℝ}
    (hX : ContinuousOn X (uIcc a b))
    (hg : ∀ t ∈ uIcc a b, |g (X t)-g (X a)| ≤ ε) :
    ∀ z ∈ uIcc (X a) (X b), |g z-g (X a)| ≤ ε := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := intermediate_value_uIcc hX hz
  exact hg t ht

/-- The weighted Cauchy--Schwarz inequality actually used to remove the
mixed A,M term, including weights of either sign. -/
theorem weighted_mixed_cauchy_schwarz {ι : Type*} (s : Finset ι) (h a m : ι → ℝ) :
    (∑ j ∈ s, h j*a j*m j)^2 ≤
      (∑ j ∈ s, |h j| * (a j)^2) * (∑ j ∈ s, |h j| * (m j)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  intro j hj
  apply le_of_eq
  calc
    _ = (h j)^2 * (a j)^2 * (m j)^2 := by ring
    _ = _ := by rw [← sq_abs (h j)]; ring

end Asakura.Chapter3Written
