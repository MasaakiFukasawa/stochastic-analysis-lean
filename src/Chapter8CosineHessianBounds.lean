import Chapter8CosineExample
import Chapter8FrictionScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped BigOperators
namespace Asakura.Chapter8

/-- The cosine perturbation changes every Hessian quadratic form by at most
|c| times the Euclidean squared norm. -/
theorem cosine_hessian_quadratic_bounds {d : ℕ} (k c : ℝ) (q z : Fin d → ℝ) :
    (k-|c|)*(∑ i,z i^2) ≤ ∑ i,(k+c*Real.cos (q i))*z i^2 ∧
    (∑ i,(k+c*Real.cos (q i))*z i^2) ≤ (k+|c|)*(∑ i,z i^2) := by
  have hb i : -|c|≤c*Real.cos (q i) ∧ c*Real.cos (q i)≤|c| := by
    apply abs_le.mp
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg c)).trans_eq (mul_one _)
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by linarith [(hb i).1]) (sq_nonneg _)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by linarith [(hb i).2]) (sq_nonneg _)

/-- Direct verification of the monotonicity condition, without presuming that
an informal Hessian calculation already implies the desired inequality. -/
theorem cosine_gradient_strong_monotonicity {d : ℕ} (k c : ℝ) (x y : Fin d → ℝ) :
    (k-|c|)*(∑ i,(x i-y i)^2) ≤
      ∑ i,(x i-y i)*((k*x i+c*Real.sin (x i))-(k*y i+c*Real.sin (y i))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hb : |c*(x i-y i)*(Real.sin (x i)-Real.sin (y i))|≤|c| *(x i-y i)^2 := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ (|c| *|x i-y i|)*|x i-y i| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (by positivity)
      _ = _ := by rw [mul_assoc,←sq_abs]; ring
  have hh := (abs_le.mp hb).1
  nlinarith

theorem cosine_newton_friction (k c m γ : ℝ) (hk : |c|<k) (hm : 0<m)
    (hγ : Real.sqrt m*(Real.sqrt (k+|c|)-Real.sqrt (k-|c|))<γ) :
    0<(k-|c|)/m ∧ (k-|c|)/m≤(k+|c|)/m ∧
      Real.sqrt ((k+|c|)/m)-Real.sqrt ((k-|c|)/m)<γ/m := by
  refine ⟨div_pos (sub_pos.mpr hk) hm,?_,?_⟩
  · apply div_le_div_of_nonneg_right _ hm.le
    linarith [abs_nonneg c]
  · exact newton_friction_rescaling m γ (k-|c|) (k+|c|) hm
      (sub_pos.mpr hk).le (by linarith [abs_nonneg c]) hγ

end Asakura.Chapter8
