import Chapter8WeightedCoupling

open MeasureTheory Finset
open scoped BigOperators NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem lipschitz_scalar_linear_bound {E : Type*} [NormedAddCommGroup E]
    (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (x : E) :
    |f x| ≤ (|f 0|+(L:ℝ)+1)*(1+‖x‖) := by
  have hh := hf.norm_sub_le x 0
  simp only [Real.norm_eq_abs,sub_zero] at hh
  have ht := abs_add_le (f x-f 0) (f 0)
  rw [sub_add_cancel] at ht
  have h1 : 0 ≤ |f 0| * ‖x‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  nlinarith [L.coe_nonneg,norm_nonneg x]

/-- Products of Lipschitz coefficients have exactly the weighted
Lipschitz estimate used for nonstationary information entries. -/
theorem lipschitz_product_weighted_bound {E : Type*} [NormedAddCommGroup E]
    (f g : E → ℝ) (L K : ℝ≥0) (hf : LipschitzWith L f) (hg : LipschitzWith K g) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x y,|f x*g x-f y*g y| ≤ C*‖x-y‖*(1+‖x‖+‖y‖) := by
  let A := |f 0|+(L:ℝ)+1
  let B := |g 0|+(K:ℝ)+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hLA : (L:ℝ) ≤ A := by dsimp [A]; linarith [abs_nonneg (f 0)]
  have hKB : (K:ℝ) ≤ B := by dsimp [B]; linarith [abs_nonneg (g 0)]
  refine ⟨2*A*B,by positivity,?_⟩
  intro x y
  have hfx := lipschitz_scalar_linear_bound f L hf x
  have hgy := lipschitz_scalar_linear_bound g K hg y
  change |f x| ≤ A*(1+‖x‖) at hfx
  change |g y| ≤ B*(1+‖y‖) at hgy
  have hfd : |f x-f y| ≤ A*‖x-y‖ :=
    (hf.norm_sub_le x y).trans (mul_le_mul_of_nonneg_right hLA (norm_nonneg _))
  have hgd : |g x-g y| ≤ B*‖x-y‖ :=
    (hg.norm_sub_le x y).trans (mul_le_mul_of_nonneg_right hKB (norm_nonneg _))
  calc
    _ = |f x*(g x-g y)+g y*(f x-f y)| := by congr 1; ring
    _ ≤ |f x| * |g x-g y|+|g y| * |f x-f y| := by
      simpa only [abs_mul] using abs_add_le (f x*(g x-g y)) (g y*(f x-f y))
    _ ≤ (A*(1+‖x‖))*(B*‖x-y‖)+(B*(1+‖y‖))*(A*‖x-y‖) :=
      add_le_add (mul_le_mul hfx hgd (abs_nonneg _) (by positivity))
        (mul_le_mul hgy hfd (abs_nonneg _) (by positivity))
    _ = A*B*‖x-y‖*(2+‖x‖+‖y‖) := by ring
    _ ≤ 2*A*B*‖x-y‖*(1+‖x‖+‖y‖) := by
      have hh := mul_le_mul_of_nonneg_left
        (show 2+‖x‖+‖y‖ ≤ 2*(1+‖x‖+‖y‖) from by linarith [norm_nonneg x,norm_nonneg y])
        (show 0 ≤ A*B*‖x-y‖ by positivity)
      nlinarith only [hh]

theorem information_entry_weighted_bound {E : Type*} [NormedAddCommGroup E]
    {d : ℕ} (f g : Fin d → E → ℝ) (L K : Fin d → ℝ≥0)
    (hf : ∀ j,LipschitzWith (L j) (f j)) (hg : ∀ j,LipschitzWith (K j) (g j)) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x y,
      |(∑ j,f j x*g j x)-(∑ j,f j y*g j y)| ≤ C*‖x-y‖*(1+‖x‖+‖y‖) := by
  choose C hC hb using fun j => lipschitz_product_weighted_bound (f j) (g j) (L j) (K j) (hf j) (hg j)
  refine ⟨∑ j,C j,Finset.sum_nonneg (fun j _ => hC j),?_⟩
  intro x y
  rw [← Finset.sum_sub_distrib]
  have hh := (Finset.abs_sum_le_sum_abs (fun j => f j x*g j x-f j y*g j y) Finset.univ).trans
    (Finset.sum_le_sum (fun j _ => hb j x y))
  simpa only [Finset.sum_mul] using hh

end Asakura.Chapter8
