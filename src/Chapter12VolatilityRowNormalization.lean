import Chapter12BrownianUnitDirection
import Chapter12BasketMatrixHedge
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 1600000

theorem volatility_row_normalization {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det≠0) (i : Fin d) :
    let σ := Real.sqrt (∑ j,A i j^2)
    0<σ ∧ σ^2=∑ j,A i j^2 ∧ (∑ j,(A i j/σ)^2)=1 ∧ ∀ j,σ*(A i j/σ)=A i j := by
  intro σ
  have hs0 : 0≤∑ j,A i j^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hs : 0<∑ j,A i j^2 := by
    by_contra h
    have hz : ∑ j,A i j^2=0 := le_antisymm (not_lt.mp h) hs0
    apply hA (Matrix.det_eq_zero_of_row_eq_zero i _)
    intro j
    have hle : A i j^2≤∑ k,A i k^2 := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    rw [hz] at hle
    nlinarith [sq_nonneg (A i j)]
  have hp : 0<σ := Real.sqrt_pos.mpr hs
  have hsq : σ^2=∑ j,A i j^2 := Real.sq_sqrt hs0
  refine ⟨hp,hsq,?_,fun j => ?_⟩
  · simp_rw [div_pow]
    rw [←Finset.sum_div,←hsq,div_self (pow_ne_zero 2 hp.ne')]
  · field_simp
end Asakura.Chapter12
#print axioms Asakura.Chapter12.volatility_row_normalization
