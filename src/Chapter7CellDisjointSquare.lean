import Chapter7BrownianGridIntegrand

open MeasureTheory Set Finset
open scoped BigOperators
namespace Asakura.Chapter7
open Asakura.Chapter4
set_option maxHeartbeats 1000000

lemma uniform_cells_disjoint (h r : ℝ) (hh : 0≤h) (i j : ℕ) (hij : i≠j)
    (hi : r ∈ Ioc ((i:ℝ)*h) (((i:ℝ)+1)*h)) :
    r ∉ Ioc ((j:ℝ)*h) (((j:ℝ)+1)*h) := by
  intro hj
  rcases lt_or_gt_of_ne hij with hc | hc
  · have hn : (i:ℝ)+1≤ j := by exact_mod_cast (Nat.succ_le_of_lt hc)
    have he := mul_le_mul_of_nonneg_right hn hh
    exact (not_lt_of_ge (hi.2.trans he)) hj.1
  · have hn : (j:ℝ)+1≤ i := by exact_mod_cast (Nat.succ_le_of_lt hc)
    have he := mul_le_mul_of_nonneg_right hn hh
    exact (not_lt_of_ge (hj.2.trans he)) hi.1

lemma brownian_grid_square {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (h : ℝ) (hh : 0≤h) (n : ℕ) (z : Ω × ℝ) :
    (brownianGridIntegrand B u h n z)^2=
      ∑ k : Fin n,(brownianCellIntegrand B u ((k:ℝ)*h) (((k:ℝ)+1)*h) z)^2 := by
  classical
  let X := fun k : Fin n => brownianCellIntegrand B u ((k:ℝ)*h) (((k:ℝ)+1)*h) z
  have hcross (i j : Fin n) (hij : i≠j) : X i*X j=0 := by
    have hij' : i.val≠j.val := fun he => hij (Fin.ext he)
    by_cases hi : z.2 ∈ Ioc ((i:ℝ)*h) (((i:ℝ)+1)*h)
    · have hj := uniform_cells_disjoint h z.2 hh i.val j.val hij' hi
      simp only [X,brownianCellIntegrand,indicator_of_notMem hj,mul_zero]
    · simp only [X,brownianCellIntegrand,indicator_of_notMem hi,zero_mul]
  change (∑ k,X k)^2=∑ k,(X k)^2
  simp only [pow_two,Finset.sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  exact sum_eq_single_of_mem i hi (fun j _ hji => hcross i j hji.symm)

end Asakura.Chapter7
