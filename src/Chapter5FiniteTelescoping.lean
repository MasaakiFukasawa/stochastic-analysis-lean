import Chapter5MartingaleTelescoping

open MeasureTheory Filter
open scoped BigOperators
namespace Asakura.Chapter5

/-- Finite Gaussian steps share one null set and telescope in reverse
observation order. -/
theorem finite_ae_reverse_telescope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (V : ℕ → Ω → ℝ) (D : Fin N → Ω → ℝ)
    (h : ∀ j : Fin N,V j.val =ᵐ[P] fun w => V (j.val+1) w+D j w) :
    V 0 =ᵐ[P] fun w => V N w+∑ j,D j w := by
  filter_upwards [ae_all_iff.mpr h] with w hw
  have hs : (∑ j : Fin N,(V j.val w-V (j.val+1) w))=V 0 w-V N w := by
    rw [Fin.sum_univ_eq_sum_range (fun j => V j w-V (j+1) w) N]
    exact Finset.sum_range_sub' (fun j => V j w) N
  have he : (∑ j : Fin N,D j w)=V 0 w-V N w := by
    rw [← hs]
    apply Finset.sum_congr rfl
    intro j _
    linarith only [hw j]
  linarith only [he]

end Asakura.Chapter5
