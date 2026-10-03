import Chapter8SDEGeneratorInterface
import Chapter8GibbsC2Generator

open MeasureTheory
open scoped BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000

/-- The actual Ito generator agrees with the divergence-form generator
under the Einstein relation, including singular mobility matrices. -/
theorem gibbs_generator_identification {d n : ℕ}
    (U' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ)
    (M : Fin d → Fin d → ℝ) (σ : Fin d → Fin n → ℝ) (β : ℝ)
    (hM : ∀ i j,M i j=M j i)
    (hσ : ∀ i j,∑ k,σ i k*σ j k=2*β⁻¹*M i j)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    coordinateGenerator (fun i y => -(∑ j,M i j*U' y (Pi.single j 1)))
      (fun i j _ => σ i j) f x =
      ∑ i,∑ j,M i j*(-U' x (Pi.single i 1)*fderiv ℝ f x (Pi.single j 1)+
        β⁻¹*fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) := by
  unfold coordinateGenerator
  simp_rw [hσ]
  have hd : (∑ i,fderiv ℝ f x (Pi.single i 1)* -(∑ j,M i j*U' x (Pi.single j 1)))=
      ∑ i,∑ j,M i j*(-U' x (Pi.single i 1)*fderiv ℝ f x (Pi.single j 1)) := by
    simp only [mul_neg,Finset.mul_sum,← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM j i]
    ring
  rw [hd]
  simp only [Finset.sum_div,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Asakura.Chapter8
