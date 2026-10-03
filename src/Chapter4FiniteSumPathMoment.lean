import Chapter4VectorPaths
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma finite_sum_path_square {E : Type*} [NormedAddCommGroup E] {n : ℕ} (X : Fin n → E) :
    ‖∑ i,X i‖^2≤(n:ℝ)*∑ i,‖X i‖^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖X i‖)
  simpa only [Finset.card_univ,Fintype.card_fin] using
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans h

lemma finite_sum_path_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) {n : ℕ} (X : Fin n → Ω → E) (hi : ∀ i,MemLp (X i) 2 P) :
    MemLp (fun w => ∑ i,X i w) 2 P ∧
      (∫ w,‖∑ i,X i w‖^2 ∂P)≤(n:ℝ)*∑ i,∫ w,‖X i w‖^2 ∂P := by
  have hs : MemLp (fun w => ∑ i,X i w) 2 P := by
    convert memLp_finsetSum' Finset.univ (fun i _ => hi i) using 1
    ext w
    simp
  refine ⟨hs,?_⟩
  rw [← integral_finsetSum Finset.univ (fun i _ => (hi i).integrable_norm_pow (by norm_num : (2:ℕ)≠0)),← integral_const_mul]
  apply integral_mono (hs.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((integrable_finsetSum Finset.univ (fun i _ => (hi i).integrable_norm_pow (by norm_num : (2:ℕ)≠0))).const_mul _)
  exact fun w => finite_sum_path_square (fun i => X i w)

end Asakura.Chapter4
