import Chapter7BrownianClockCells

open MeasureTheory Set Filter
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000

lemma clock_cell_truncation (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n)
    (i : Fin (n+1)) :
    clockCellLength T t n i=max 0 (min (T/n) (t-(i:ℝ)*(T/n))) := by
  let h := T/(n:ℝ)
  let k := ⌊t/h⌋₊
  have hh : 0<h := div_pos hT (by exact_mod_cast hn)
  have hd := grid_time_decomposition T t hT ht0 htT n hn
  change k≤n ∧ 0≤t-(k:ℝ)*h ∧ t-(k:ℝ)*h<h ∧ t=(k:ℝ)*h+(t-(k:ℝ)*h) at hd
  have hlo : (k:ℝ)*h≤t := by linarith [hd.2.1]
  have hhi : t<((k:ℝ)+1)*h := by nlinarith [hd.2.2.1]
  change (if i.val<k then h else if i.val=k then t-(k:ℝ)*h else 0)=max 0 (min h (t-(i:ℝ)*h))
  split_ifs with hik hik'
  · have hic : (i:ℝ)+1≤ k := by exact_mod_cast (Nat.succ_le_of_lt hik)
    have hmul := mul_le_mul_of_nonneg_right hic hh.le
    have ht : h≤t-(i:ℝ)*h := by nlinarith
    rw [min_eq_left ht,max_eq_right hh.le]
  · have he : (i:ℝ)=(k:ℝ) := by exact_mod_cast hik'
    rw [he,min_eq_right (by nlinarith : t-(k:ℝ)*h≤h),max_eq_right (sub_nonneg.mpr hlo)]
  · have hic : (k:ℝ)+1≤ i := by exact_mod_cast (show k+1≤ i.val by omega)
    have hmul := mul_le_mul_of_nonneg_right hic hh.le
    have ht : t-(i:ℝ)*h≤0 := by nlinarith
    rw [max_eq_left ((min_le_right _ _).trans ht)]

end Asakura.Chapter7
