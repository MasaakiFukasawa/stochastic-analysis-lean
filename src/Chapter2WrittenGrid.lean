import Chapter2WrittenCorrections
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter
open scoped Topology
namespace Asakura.Chapter2Written

noncomputable def upperDyadic (n : ℕ) (x : ℝ) : ℝ :=
  (Int.ceil ((2 : ℝ)^n*x) : ℝ)/(2 : ℝ)^n
noncomputable def correctedGrid (T : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ (n : ℝ) then min (upperDyadic n x) T else T

theorem upperDyadic_bounds (n : ℕ) (x : ℝ) :
    x ≤ upperDyadic n x ∧ upperDyadic n x ≤ x + 1/(2 : ℝ)^n := by
  have hp : (0 : ℝ) < 2^n := by positivity
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa [mul_comm] using Int.le_ceil ((2 : ℝ)^n*x)
  · apply (div_le_iff₀ hp).mpr
    have hc := (Int.ceil_lt_add_one ((2 : ℝ)^n*x)).le
    have he : (x + 1/(2 : ℝ)^n)*(2 : ℝ)^n = (2 : ℝ)^n*x+1 := by field_simp
    rwa [he]

theorem upperDyadic_antitone (x : ℝ) : Antitone (fun n => upperDyadic n x) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : (0 : ℝ) < 2^(n+1) := by positivity
  have hc : Int.ceil ((2 : ℝ)^(n+1)*x) ≤ 2*Int.ceil ((2 : ℝ)^n*x) := by
    apply Int.ceil_le.mpr
    push_cast
    rw [pow_succ]
    nlinarith [Int.le_ceil ((2 : ℝ)^n*x)]
  calc
    upperDyadic (n+1) x ≤ (2*(Int.ceil ((2 : ℝ)^n*x) : ℝ))/(2 : ℝ)^(n+1) := by
      apply div_le_div_of_nonneg_right _ hp.le
      exact_mod_cast hc
    _ = upperDyadic n x := by unfold upperDyadic; rw [pow_succ]; field_simp

/-- The corrected finite-horizon g_n actually takes values in D_n^T. -/
theorem correctedGrid_range (T : ℝ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    correctedGrid T n x = T ∨ ∃ j : ℤ,
      0 ≤ j ∧ j ≤ (n : ℤ)*2^n ∧ correctedGrid T n x = (j : ℝ)/(2 : ℝ)^n := by
  by_cases hn : x ≤ (n : ℝ)
  · by_cases hT : upperDyadic n x ≤ T
    · refine Or.inr ⟨Int.ceil ((2 : ℝ)^n*x), Int.ceil_nonneg (mul_nonneg (by positivity) hx), ?_, ?_⟩
      · apply Int.ceil_le.mpr
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 2^n by positivity)]
      · rw [correctedGrid, ite_eq_left hn]
        exact min_eq_left hT
    · exact Or.inl (by simp [correctedGrid, hn, min_eq_right (le_of_not_ge hT)])
  · exact Or.inl (by simp [correctedGrid, hn])

theorem correctedGrid_antitone (T x : ℝ) : Antitone (fun n => correctedGrid T n x) := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : x ≤ (n : ℝ)
  · have hn' : x ≤ ((n+1 : ℕ) : ℝ) := by push_cast; linarith
    simp only [correctedGrid, ite_eq_left hn, ite_eq_left hn']
    exact min_le_min ((upperDyadic_antitone x) (Nat.le_succ n)) le_rfl
  · unfold correctedGrid
    rw [ite_eq_right hn]
    split_ifs <;> simp [min_le_right]

/-- Both estimates used to pass to the limit hold once n≥x. -/
theorem correctedGrid_bounds {T x : ℝ} (hxT : x ≤ T) {n : ℕ} (hn : x ≤ (n : ℝ)) :
    x ≤ correctedGrid T n x ∧ correctedGrid T n x ≤ x + 1/(2 : ℝ)^n := by
  rw [correctedGrid, ite_eq_left hn]
  exact ⟨le_min (upperDyadic_bounds n x).1 hxT,
    (min_le_left _ _).trans (upperDyadic_bounds n x).2⟩

/-- The mesh error tends to zero, so the finite-horizon corrected grids converge. -/
theorem correctedGrid_tendsto {T x : ℝ} (hxT : x ≤ T) :
    Tendsto (fun n => correctedGrid T n x) atTop (𝓝 x) := by
  have he : Tendsto (fun n : ℕ => 1/(2 : ℝ)^n) atTop (𝓝 0) := by
    simpa [one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num))
  have hn : ∀ᶠ n : ℕ in atTop, x ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n => x + 1/(2 : ℝ)^n) atTop (𝓝 x) by simpa using tendsto_const_nhds.add he)
  · filter_upwards [hn] with n hn
    exact (correctedGrid_bounds hxT hn).1
  · filter_upwards [hn] with n hn
    exact (correctedGrid_bounds hxT hn).2

/-- Rounding up preserves the lower level set at each dyadic grid point. -/
theorem upperDyadic_le_grid (n : ℕ) (x : ℝ) (j : ℤ) :
    upperDyadic n x ≤ (j : ℝ)/(2 : ℝ)^n ↔ x ≤ (j : ℝ)/(2 : ℝ)^n := by
  have hp : (0 : ℝ) < 2^n := by positivity
  have hc : (Int.ceil ((2 : ℝ)^n*x) : ℝ) ≤ (j : ℝ) ↔ (2 : ℝ)^n*x ≤ (j : ℝ) := by
    exact_mod_cast (Int.ceil_le (a := (2 : ℝ)^n*x) (z := j))
  rw [upperDyadic, div_le_div_iff_of_pos_right hp, hc, le_div_iff₀ hp, mul_comm]

/-- This is the exact set identity proving the corrected τ_n is a stopping time. -/
theorem correctedGrid_le_grid (T : ℝ) (n : ℕ) (x : ℝ) (j : ℤ)
    (hj : j ≤ (n : ℤ)*2^n) (hT : (j : ℝ)/(2 : ℝ)^n < T) :
    correctedGrid T n x ≤ (j : ℝ)/(2 : ℝ)^n ↔ x ≤ (j : ℝ)/(2 : ℝ)^n := by
  have hp : (0 : ℝ) < 2^n := by positivity
  have hjn : (j : ℝ)/(2 : ℝ)^n ≤ (n : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    exact_mod_cast hj
  by_cases hn : x ≤ (n : ℝ)
  · simp only [correctedGrid, ite_eq_left hn, min_le_iff,
      not_le.mpr hT, or_false, upperDyadic_le_grid]
  · have hx : ¬ x ≤ (j : ℝ)/(2 : ℝ)^n := fun h => hn (h.trans hjn)
    simp [correctedGrid, hn, hx, not_le.mpr hT]

end Asakura.Chapter2Written
