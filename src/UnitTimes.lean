import BrownianCube

open Set
namespace Asakura
noncomputable def unitTime (k : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (t - k))

lemma unitTime_mem (k : ℕ) (t : ℝ) : unitTime k t ∈ Icc 0 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma unitTime_zero (k : ℕ) {t : ℝ} (h : t ≤ k) : unitTime k t = 0 := by
  unfold unitTime
  exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr h))

lemma unitTime_monotone (k : ℕ) : Monotone (unitTime k) := by
  intro s t h
  exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right h _))

lemma unitTime_sum (N : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range N, unitTime k t = min (N : ℝ) (max 0 t) := by
  induction N with
  | zero => simp [min_eq_left (le_max_left 0 t)]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold unitTime
    push_cast
    simp only [min_def, max_def]
    split_ifs <;> linarith

lemma unitTime_min_sum (N : ℕ) (s t : ℝ) (hs : s ∈ Icc 0 (N : ℝ)) (ht : t ∈ Icc 0 (N : ℝ)) :
    ∑ k ∈ Finset.range N, min (unitTime k s) (unitTime k t) = min s t := by
  rcases le_total s t with h | h
  · simp_rw [min_eq_left ((unitTime_monotone _) h)]
    rw [unitTime_sum, max_eq_right hs.1, min_eq_right hs.2, min_eq_left h]
  · simp_rw [min_eq_right ((unitTime_monotone _) h)]
    rw [unitTime_sum, max_eq_right ht.1, min_eq_right ht.2, min_eq_right h]

noncomputable def unitTimeCube (k : ℕ) (t : ℝ) : UnitCube 1 :=
  ⟨fun _ => unitTime k t, fun _ => unitTime_mem k t⟩

lemma unitTime_lipschitz (k : ℕ) : LipschitzWith 1 (unitTime k) := by
  have h : LipschitzWith 1 (fun t : ℝ => t - k) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp [Real.dist_eq]
  exact h.const_min 1 |>.const_max 0

lemma unitTimeCube_lipschitz (k : ℕ) : LipschitzWith 1 (unitTimeCube k) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [unitCube_one_distance]
  exact (unitTime_lipschitz k).dist_le_mul s t
end Asakura
