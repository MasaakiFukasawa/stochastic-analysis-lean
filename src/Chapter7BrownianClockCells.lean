import Chapter7BrownianBlockGridVariance
import Chapter7BrownianBlockGridMean
import Chapter7GridCellLengths
import Chapter7MeanSquareRate

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Cell lengths at a fixed observation time. The extra last cell permits
one formula at the endpoint as well. -/
noncomputable def clockCellLength (T t : ℝ) (n : ℕ) (i : Fin (n+1)) : ℝ :=
  let h := T/(n:ℝ)
  let k := ⌊t/h⌋₊
  if i.val < k then h else if i.val=k then t-(k:ℝ)*h else 0

lemma clock_cell_length_bounds (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n) :
    ∀ i,0 ≤ clockCellLength T t n i ∧ clockCellLength T t n i ≤ T/n := by
  have hd := grid_time_decomposition T t hT ht0 htT n hn
  have hh : 0 ≤ T/(n:ℝ) := div_nonneg hT.le (Nat.cast_nonneg _)
  intro i
  dsimp only [clockCellLength]
  split_ifs
  · exact ⟨hh,le_rfl⟩
  · exact ⟨hd.2.1,hd.2.2.1.le⟩
  · exact ⟨le_rfl,hh⟩

lemma clock_cell_square_sum (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n) :
    (∑ i : Fin (n+1),(clockCellLength T t n i)^2)=
      (⌊t/(T/n)⌋₊:ℝ)*(T/n)^2+(t-(⌊t/(T/n)⌋₊:ℝ)*(T/n))^2 := by
  have hd := grid_time_decomposition T t hT ht0 htT n hn
  simpa only [clockCellLength,← Fin.sum_univ_eq_sum_range] using
    completed_cell_square_sum n ⌊t/(T/n)⌋₊ hd.1 (T/n) (t-(⌊t/(T/n)⌋₊:ℝ)*(T/n))

end Asakura.Chapter7
