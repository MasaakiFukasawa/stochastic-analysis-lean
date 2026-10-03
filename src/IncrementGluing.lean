import ContinuousGluing

open Set
open scoped NNReal
namespace Asakura

noncomputable def intervalTime (k : ℕ) (s : UnitCube 1) : ℝ≥0 :=
  (k:ℝ≥0) + ⟨s.val 0,(s.property 0).1⟩

lemma intervalTime_distance (k : ℕ) (s t : UnitCube 1) :
    dist (intervalTime k s) (intervalTime k t) = dist s t := by
  rw [unitCube_one_distance]
  change |((k:ℝ)+s.val 0)-((k:ℝ)+t.val 0)| = _
  congr 1
  ring

lemma intervalTime_zero (k : ℕ) : intervalTime k cubeZero = k := by
  apply NNReal.coe_injective
  change (k:ℝ)+0 = (k:ℝ)
  ring

lemma clamped_increment (X : ℝ≥0 → ℝ) (k : ℕ) (t : ℝ≥0) :
    X (intervalTime k (unitTimeCube k t))-X k = X (min t (k+1))-X (min t k) := by
  by_cases htk : t ≤ k
  · rw [unitTimeCube_zero k (by exact_mod_cast htk),intervalTime_zero,
      min_eq_left htk,min_eq_left (htk.trans (by exact_mod_cast Nat.le_succ k))]
    simp
  · have hkt : (k:ℝ≥0) ≤ t := le_of_not_ge htk
    have he : intervalTime k (unitTimeCube k t) = min t (k+1) := by
      apply NNReal.coe_injective
      change (k:ℝ)+max 0 (min 1 ((t:ℝ)-k)) = min (t:ℝ) ((k:ℝ)+1)
      have hkt' : (k:ℝ) ≤ t := by exact_mod_cast hkt
      rw [max_eq_right (le_min (by norm_num) (sub_nonneg.mpr hkt'))]
      by_cases ht : (t:ℝ) ≤ (k:ℝ)+1
      · rw [min_eq_right (by linarith : (t:ℝ)-k ≤ 1),min_eq_left ht]
        ring
      · rw [min_eq_left (by linarith : 1 ≤ (t:ℝ)-k),min_eq_right (le_of_not_ge ht)]
    rw [he,min_eq_right hkt]

lemma clamped_increment_sum (X : ℝ≥0 → ℝ) (N : ℕ) (t : ℝ≥0) (ht : t ≤ N) :
    (∑ k ∈ Finset.range N, (X (intervalTime k (unitTimeCube k t))-X k)) = X t-X 0 := by
  simp_rw [clamped_increment]
  have he : ∀ n : ℕ, (∑ k ∈ Finset.range n, (X (min t (k+1))-X (min t k))) =
      X (min t n)-X (min t 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring
  rw [he,min_eq_left ht,min_eq_right (by positivity : (0:ℝ≥0)≤t)]
end Asakura
