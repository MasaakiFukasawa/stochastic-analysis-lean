import Chapter7BrownianClockCells

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

noncomputable def brownianCellClock {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T t : ℝ) (n : ℕ) (w : Ω) : ℝ :=
  (4*(n:ℝ)/T^2)*∑ k : Fin (n+1),∫ r in 0..clockCellLength T t n k,
    (∑ j,u j*(B.W j (realTimeClamp ((k:ℝ)*(T/n)+r)) w-
      B.W j (realTimeClamp ((k:ℝ)*(T/n))) w))^2

lemma brownian_cell_clock_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (T t : ℝ) (n : ℕ) (hT : 0<T) (ht0 : 0≤t) (htT : t≤T) (hn : 0<n) :
    MemLp (brownianCellClock B u T t n) 2 P ∧
    |(∫ w,brownianCellClock B u T t n w ∂P)-(2*(∑ j,u j^2)/T)*t| ≤ 2*(∑ j,u j^2)/n := by
  have hl := clock_cell_length_bounds T t n hT ht0 htT hn
  have hm := brownian_block_grid_mean P B u u (fun k : Fin (n+1) => (k:ℝ)*(T/n))
    (clockCellLength T t n) (fun k => mul_nonneg (by positivity) (div_nonneg hT.le (Nat.cast_nonneg _))) (fun k => (hl k).1)
  have hs : (∑ j,u j*u j)=(∑ j,u j^2) := by simp only [pow_two]
  have hm' : MemLp (fun w => ∑ k : Fin (n+1),∫ r in 0..clockCellLength T t n k,
      (∑ j,u j*(B.W j (realTimeClamp ((k:ℝ)*(T/n)+r)) w-B.W j (realTimeClamp ((k:ℝ)*(T/n))) w))^2) 2 P := by
    simpa only [pow_two] using hm.1
  refine ⟨hm'.const_mul _,?_⟩
  simp only [brownianCellClock,integral_const_mul]
  have he := hm.2
  simp only [← pow_two,hs] at he
  rw [he,clock_cell_square_sum T t n hT ht0 htT hn]
  have hd := grid_time_decomposition T t hT ht0 htT n hn
  have hb := bracket_grid_bias n hn T (∑ j,u j^2) (t-(⌊t/(T/n)⌋₊:ℝ)*(T/n)) hT
    (sum_nonneg (fun _ _ => sq_nonneg _)) hd.2.1 hd.2.2.1.le ⌊t/(T/n)⌋₊
  have hx : (⌊t/(T/n)⌋₊:ℝ)*(T/n)+(t-(⌊t/(T/n)⌋₊:ℝ)*(T/n))=t := by ring
  rw [hx] at hb
  convert hb using 1 <;> congr 1 <;> ring

end Asakura.Chapter7
