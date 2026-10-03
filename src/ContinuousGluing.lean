import UnitTimes

open Set Filter
open scoped Topology
namespace Asakura

noncomputable def cubeZero : UnitCube 1 := ⟨fun _ => 0, fun _ => by constructor <;> norm_num⟩

lemma unitTimeCube_zero (k : ℕ) {t : ℝ} (h : t ≤ k) : unitTimeCube k t = cubeZero := by
  apply Subtype.ext
  funext i
  exact unitTime_zero k h

/-- Constant extension of each unit segment, summed to concatenate the segments. -/
noncomputable def gluedPath (F : ℕ → UnitCube 1 → ℝ) (t : ℝ) : ℝ :=
  ∑' k, F k (unitTimeCube k t)

lemma gluedPath_eq_sum (F : ℕ → UnitCube 1 → ℝ) (hF : ∀ k, F k cubeZero = 0)
    (N : ℕ) (t : ℝ) (ht : t ≤ N) :
    gluedPath F t = ∑ k ∈ Finset.range N, F k (unitTimeCube k t) := by
  apply tsum_eq_sum
  intro k hk
  rw [unitTimeCube_zero k (ht.trans (by exact_mod_cast (Nat.le_of_not_lt (by simpa using hk)))), hF]

lemma gluedPath_continuous (F : ℕ → UnitCube 1 → ℝ) (hF : ∀ k, F k cubeZero = 0)
    (hcont : ∀ k, Continuous (F k)) : Continuous (gluedPath F) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have hc : Continuous (fun u : ℝ => ∑ k ∈ Finset.range N, F k (unitTimeCube k u)) := by
    apply continuous_finset_sum
    intro k hk
    exact (hcont k).comp (unitTimeCube_lipschitz k).continuous
  apply hc.continuousAt.congr
  filter_upwards [Iio_mem_nhds hN] with u hu
  exact (gluedPath_eq_sum F hF N u hu.le).symm

lemma gluedPath_holder (F : ℕ → UnitCube 1 → ℝ) (hF : ∀ k, F k cubeZero = 0)
    (α : ℝ) (hα : 0 ≤ α) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hH : ∀ k s t, dist (F k s) (F k t) ≤ C k * (dist s t)^α)
    (N : ℕ) (s t : ℝ) (hs : s ≤ N) (ht : t ≤ N) :
    dist (gluedPath F s) (gluedPath F t) ≤
      (∑ k ∈ Finset.range N, C k) * (dist s t)^α := by
  rw [gluedPath_eq_sum F hF N s hs, gluedPath_eq_sum F hF N t ht]
  calc
    _ ≤ ∑ k ∈ Finset.range N, dist (F k (unitTimeCube k s)) (F k (unitTimeCube k t)) :=
      dist_sum_sum_le _ _ _
    _ ≤ ∑ k ∈ Finset.range N, C k * (dist s t)^α := by
      apply Finset.sum_le_sum
      intro k hk
      apply (hH k _ _).trans
      apply mul_le_mul_of_nonneg_left _ (hC k)
      apply Real.rpow_le_rpow dist_nonneg _ hα
      simpa using (unitTimeCube_lipschitz k).dist_le_mul s t
    _ = _ := (Finset.sum_mul _ _ _).symm
end Asakura
