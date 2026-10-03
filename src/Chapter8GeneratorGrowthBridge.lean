import Chapter8GeneratorLinearGrowth

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1100000

theorem pi_norm_le_euclidean {d : ℕ} (x : Fin d → ℝ) :
    ‖x‖≤Real.sqrt (∑ i,x i^2) := by
  have hh := Asakura.Chapter3Complete.pi_norm_sq_le_sum_sq x
  have hs : 0≤∑ i,x i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he := Real.sq_sqrt hs
  nlinarith [norm_nonneg x,Real.sqrt_nonneg (∑ i,x i^2)]

theorem bounded_linear_polynomial_growth {d : ℕ}
    (f G : (Fin d → ℝ) → ℝ) (A C : ℝ) (hC : 0≤C)
    (hf : ∀ x,‖f x‖≤A) (hG : ∀ x,|G x|≤C*(1+‖x‖)) :
    ∃ K : ℝ,0≤K ∧
      (∀ x,|f x|≤K*(1+(Real.sqrt (∑ i,x i^2))^1)) ∧
      (∀ x,|G x|≤K*(1+(Real.sqrt (∑ i,x i^2))^1)) := by
  let K := max (max A C) 0
  have hK : 0≤K := le_max_right _ _
  have ha : A≤K := (le_max_left A C).trans (le_max_left _ _)
  have hc : C≤K := (le_max_right A C).trans (le_max_left _ _)
  refine ⟨K,hK,?_,?_⟩
  · intro x
    have hb : |f x|≤A := by simpa only [Real.norm_eq_abs] using hf x
    have hs := mul_nonneg hK (Real.sqrt_nonneg (∑ i,x i^2))
    simp only [pow_one]
    nlinarith
  · intro x
    simp only [pow_one]
    exact (hG x).trans (mul_le_mul hc (add_le_add le_rfl (pi_norm_le_euclidean x))
      (by positivity) hK)

end Asakura.Chapter8
