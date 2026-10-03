import Chapter7BracketGridAlgebra
import Mathlib.Algebra.Order.Floor.Semiring

open Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

/-- The completed cells and the final, possibly empty, cell at time t. -/
lemma grid_time_decomposition (T t : ℝ) (hT : 0 < T) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (n : ℕ) (hn : 0 < n) :
    let h := T/(n:ℝ)
    let k := ⌊t/h⌋₊
    k ≤ n ∧ 0 ≤ t-(k:ℝ)*h ∧ t-(k:ℝ)*h < h ∧
      t=(k:ℝ)*h+(t-(k:ℝ)*h) := by
  dsimp only
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hh : 0 < T/(n:ℝ) := div_pos hT hnR
  have ha := Nat.floor_le (div_nonneg ht0 hh.le)
  have hb := Nat.lt_floor_add_one (t/(T/(n:ℝ)))
  have hlo : (⌊t/(T/(n:ℝ))⌋₊:ℝ)*(T/(n:ℝ)) ≤ t := (le_div_iff₀ hh).mp ha
  have hhi : t < ((⌊t/(T/(n:ℝ))⌋₊:ℝ)+1)*(T/(n:ℝ)) := (div_lt_iff₀ hh).mp hb
  have hkn : (⌊t/(T/(n:ℝ))⌋₊:ℝ) ≤ n := by
    apply (mul_le_mul_iff_right₀ hh).mp
    calc
      _ ≤ t := by simpa only [mul_comm] using hlo
      _ ≤ T := htT
      _ = (T/(n:ℝ))*(n:ℝ) := by field_simp
  exact ⟨by exact_mod_cast hkn,by linarith,by nlinarith,by ring⟩

/-- This finite list also covers t=T: then k=n and the extra cell is empty. -/
lemma completed_cell_square_sum (n k : ℕ) (hk : k ≤ n) (h r : ℝ) :
    (∑ i ∈ range (n+1),(if i < k then h else if i=k then r else 0)^2)=
      (k:ℝ)*h^2+r^2 := by
  have hs : range (n+1)=range k ∪ Ico k (n+1) := by
    ext i
    simp only [mem_range,mem_union,mem_Ico]
    omega
  rw [hs,sum_union (by apply disjoint_left.mpr; intro i hi hj; simp only [mem_range,mem_Ico] at hi hj; omega)]
  have hfirst : (∑ i ∈ range k,(if i < k then h else if i=k then r else 0)^2)=(k:ℝ)*h^2 := by
    calc
      _ = ∑ _i ∈ range k,h^2 := sum_congr rfl (fun i hi => by rw [if_pos (mem_range.mp hi)])
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]
  rw [hfirst]
  congr 1
  rw [sum_eq_single k]
  · simp
  · intro i hi hik
    have hi' := mem_Ico.mp hi
    simp only [if_neg (by omega : ¬i<k),if_neg hik,zero_pow (by decide : (2:ℕ)≠0)]
  · intro hk'
    exact (hk' (mem_Ico.mpr ⟨le_rfl,by omega⟩)).elim

end Asakura.Chapter7
