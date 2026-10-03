import Chapter2WrittenGrid
import Mathlib.Topology.Instances.EReal.Lemmas

open Set Filter
open scoped Topology
namespace Asakura.Chapter2Written

/-- The manuscript's repaired map, including λ=∞ and T=∞. -/
noncomputable def extendedGrid (T : EReal) (n : ℕ) (x : EReal) : EReal :=
  if x ≤ ((n : ℝ) : EReal) then min (upperDyadic n x.toReal : EReal) T else T

theorem extendedGrid_coe (T x : ℝ) (n : ℕ) :
    extendedGrid T n x = (correctedGrid T n x : EReal) := by
  by_cases h : x ≤ (n : ℝ)
  · simp only [extendedGrid, correctedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_left h]
    by_cases hT : upperDyadic n x ≤ T
    · rw [min_eq_left hT, min_eq_left (EReal.coe_le_coe hT)]
    · rw [min_eq_right (le_of_not_ge hT), min_eq_right (EReal.coe_le_coe (le_of_not_ge hT))]
  · simp only [extendedGrid, correctedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_right h]

theorem extendedGrid_top (T : EReal) (n : ℕ) : extendedGrid T n ⊤ = T := by
  simp only [extendedGrid, top_le_iff, EReal.coe_ne_top, ite_eq_right, not_false_eq_true]

theorem upperDyadic_tendsto (x : ℝ) : Tendsto (fun n => upperDyadic n x) atTop (𝓝 x) := by
  have he : Tendsto (fun n : ℕ => 1/(2 : ℝ)^n) atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => x + 1/(2 : ℝ)^n) atTop (𝓝 x) by simpa using tendsto_const_nhds.add he)
  · exact fun n => (upperDyadic_bounds n x).1
  · exact fun n => (upperDyadic_bounds n x).2

theorem extendedGrid_bounds {T x : EReal} (hx : 0 ≤ x) (hxT : x ≤ T) (n : ℕ) :
    x ≤ extendedGrid T n x ∧ extendedGrid T n x ≤ T := by
  by_cases hn : x ≤ ((n : ℝ) : EReal)
  · have hbot : x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le (by simp) hx)
    have htop : x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hn (EReal.coe_lt_top _))
    have he := EReal.coe_toReal htop hbot
    rw [extendedGrid, ite_eq_left hn]
    refine ⟨le_min ?_ hxT, min_le_right _ _⟩
    rw [← he]
    exact EReal.coe_le_coe (upperDyadic_bounds n x.toReal).1
  · rw [extendedGrid, ite_eq_right hn]
    exact ⟨hxT, le_rfl⟩

theorem extendedGrid_antitone (T x : EReal) (hx : 0 ≤ x) :
    Antitone (fun n => extendedGrid T n x) := by
  cases x using EReal.rec with
  | bot => simp at hx
  | top => simpa [extendedGrid_top] using (antitone_const : Antitone (fun _ : ℕ => T))
  | coe x =>
    apply antitone_nat_of_succ_le
    intro n
    by_cases hn : x ≤ (n : ℝ)
    · have hn' : x ≤ ((n+1 : ℕ) : ℝ) := by push_cast; linarith
      simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_left hn, ite_eq_left hn']
      exact min_le_min (EReal.coe_le_coe ((upperDyadic_antitone x) (Nat.le_succ n))) le_rfl
    · simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_right hn]
      split_ifs <;> simp

/-- The convergence statement now includes both infinite time and infinite horizon. -/
theorem extendedGrid_tendsto {T x : EReal} (hx : 0 ≤ x) (hxT : x ≤ T) :
    Tendsto (fun n => extendedGrid T n x) atTop (𝓝 x) := by
  cases x using EReal.rec with
  | bot => simp at hx
  | top =>
    have hT : T = ⊤ := top_le_iff.mp hxT
    simp [hT, extendedGrid_top]
  | coe x =>
    have ht : Tendsto (fun n => min (upperDyadic n x : EReal) T) atTop (𝓝 (x : EReal)) := by
      simpa [min_eq_left hxT] using (EReal.tendsto_coe.mpr (upperDyadic_tendsto x)).min (tendsto_const_nhds (x := T))
    apply ht.congr'
    have hn : ∀ᶠ n : ℕ in atTop, x ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x)
    filter_upwards [hn] with n hn
    simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_left hn]

/-- Every value is the terminal point or one of finitely many nonnegative dyadic points. -/
theorem extendedGrid_range {T x : EReal} (hx : 0 ≤ x) (n : ℕ) :
    extendedGrid T n x = T ∨ ∃ j : ℤ, 0 ≤ j ∧ j ≤ (n : ℤ)*2^n ∧
      extendedGrid T n x = (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal) := by
  cases x using EReal.rec with
  | bot => simp at hx
  | top => exact Or.inl (extendedGrid_top T n)
  | coe x =>
    by_cases hn : x ≤ (n : ℝ)
    · by_cases hT : (upperDyadic n x : EReal) ≤ T
      · refine Or.inr ⟨Int.ceil ((2 : ℝ)^n*x), ?_, ?_, ?_⟩
        · apply Int.ceil_nonneg
          exact mul_nonneg (by positivity) (by exact_mod_cast hx)
        · apply Int.ceil_le.mpr
          push_cast
          nlinarith [mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 2^n by positivity)]
        · simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_left hn]
          exact min_eq_left hT
      · exact Or.inl (by simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_left hn, min_eq_right (le_of_not_ge hT)])
    · exact Or.inl (by simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_right hn])

/-- Exact lower-level identity at all nonterminal grid points, also for T=∞. -/
theorem extendedGrid_le_grid (T : EReal) (n : ℕ) {x : EReal} (hx : 0 ≤ x) (j : ℤ)
    (hj : j ≤ (n : ℤ)*2^n) (hT : (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal) < T) :
    extendedGrid T n x ≤ (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal) ↔
      x ≤ (((j : ℝ)/(2 : ℝ)^n : ℝ) : EReal) := by
  cases x using EReal.rec with
  | bot => simp at hx
  | top => simp [extendedGrid_top, not_le.mpr hT]
  | coe x =>
    have hjn : (j : ℝ)/(2 : ℝ)^n ≤ (n : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^n)).mpr
      exact_mod_cast hj
    by_cases hn : x ≤ (n : ℝ)
    · simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_left hn,
        min_le_iff, not_le.mpr hT, or_false, upperDyadic_le_grid]
    · have hxj : ¬ x ≤ (j : ℝ)/(2 : ℝ)^n := fun h => hn (h.trans hjn)
      simp only [extendedGrid, EReal.coe_le_coe_iff, EReal.toReal_coe, ite_eq_right hn, hxj, not_le.mpr hT]

end Asakura.Chapter2Written
