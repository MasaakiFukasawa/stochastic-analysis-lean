import Chapter6BoundedIntegrand

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter6

lemma finite_linear_coefficient_bound {d : ℕ} (A : Fin d → Fin d → ℝ)
    (v : Fin d → ℝ) (K : ℝ) (hK : 0 ≤ K) (hv : ∀ j,|v j| ≤ K) (i : Fin d) :
    |∑ j,A i j*v j| ≤ (∑ k,∑ j,|A k j|)*K := by
  calc
    _ ≤ ∑ j,|A i j*v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j,|A i j| *K := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = (∑ j,|A i j|)*K := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun k => ∑ j,|A k j|) (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A k j))) (Finset.mem_univ i)) hK

end Asakura.Chapter6
