import Chapter12CompositionHilbertStability

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem partition_polynomial_bound (k : ℕ) (R B : ℝ) (hR : 1≤R) (hB : 0≤B) :
    (∑c : OrderedFinpartition k,
      (B*(∏i : Fin c.length,R)+∑i : Fin c.length,B*(1*∏j∈Finset.univ.erase i,R)))≤
      (Fintype.card (OrderedFinpartition k):ℝ)*B*(k+1)*R^k := by
  classical
  have hR0 : 0≤R := zero_le_one.trans hR
  have hp (c : OrderedFinpartition k) : (∏i : Fin c.length,R)≤R^k := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_pow_right₀ hR c.length_le
  have he (c : OrderedFinpartition k) (i : Fin c.length) :
      (∏j∈Finset.univ.erase i,R)≤R^k := by
    apply le_trans _ (hp c)
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset _ _)
      (fun _ _ => hR0) (fun _ _ _ => hR)
  calc
    _ ≤ ∑c : OrderedFinpartition k,(B*R^k+(c.length:ℝ)*(B*R^k)) := by
      apply Finset.sum_le_sum
      intro c _
      apply add_le_add (mul_le_mul_of_nonneg_left (hp c) hB)
      calc
        _ ≤ ∑i : Fin c.length,B*R^k := Finset.sum_le_sum (fun i _ => by
          simp only [one_mul]
          exact mul_le_mul_of_nonneg_left (he c i) hB)
        _ = _ := by simp
    _ ≤ ∑_c : OrderedFinpartition k,B*(k+1)*R^k := by
      apply Finset.sum_le_sum
      intro c _
      have hck : (c.length:ℝ)≤k := by exact_mod_cast c.length_le
      have hmul := mul_le_mul_of_nonneg_right hck (mul_nonneg hB (pow_nonneg hR0 k))
      nlinarith
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
end Asakura.Chapter12
#print axioms Asakura.Chapter12.partition_polynomial_bound
