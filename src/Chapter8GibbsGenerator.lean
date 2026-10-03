import Chapter8GibbsDensity

open Finset
open scoped BigOperators
namespace Asakura.Chapter8

/-- The divergence identity uses symmetry of M, but not invertibility or
positive definiteness; it therefore includes the degenerate case. -/
theorem gibbs_generator_divergence_algebra {ι : Type*} [Fintype ι]
    (M H : ι → ι → ℝ) (hM : ∀ i j,M i j=M j i)
    (U f : ι → ℝ) (β ρ : ℝ) (hβ : β ≠ 0) :
    ρ*(-(∑ i,∑ j,M i j*U j*f i)+β⁻¹*(∑ i,∑ j,M i j*H i j)) =
      β⁻¹*(∑ i,∑ j,M i j*((-β*ρ*U i)*f j+ρ*H i j)) := by
  have hcross : (∑ i,∑ j,M i j*U i*f j) = ∑ i,∑ j,M i j*U j*f i := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hM j i]
  have he : (∑ i,∑ j,M i j*((-β*ρ*U i)*f j+ρ*H i j)) =
      (-β*ρ)*(∑ i,∑ j,M i j*U i*f j)+ρ*(∑ i,∑ j,M i j*H i j) := by
    simp only [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [he,hcross]
  field_simp
  <;> ring

end Asakura.Chapter8
