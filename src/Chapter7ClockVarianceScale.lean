import Chapter7BracketGridAlgebra

namespace Asakura.Chapter7

lemma clock_variance_scale (n : ℕ) (hn : 0<n) (T q : ℝ) (hT : 0<T) :
    (4*(n:ℝ)/T^2)^2*((n+1:ℕ):ℝ)*(T/n)^4*q^2 ≤ 32*q^2/n := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have he : (4*(n:ℝ)/T^2)^2*((n+1:ℕ):ℝ)*(T/n)^4*q^2 =
      16*((n:ℝ)+1)*q^2/(n:ℝ)^2 := by
    push_cast
    field_simp
    <;> ring
  rw [he]
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  have hr : (32*q^2/(n:ℝ))*(n:ℝ)^2=32*q^2*n := by field_simp <;> ring
  rw [hr]
  nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg q)]

end Asakura.Chapter7
