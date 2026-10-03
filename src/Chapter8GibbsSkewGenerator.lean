import Chapter8GibbsGeneratorIdentification
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory
open scoped BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000

/-- The antisymmetric constant part of the mobility cancels because the
actual Hessian is symmetric. This is the Hamiltonian cancellation needed
for the stochastic Newton equation. -/
theorem gibbs_skew_generator_identification {d n : ℕ}
    (U' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ)
    (M : Fin d → Fin d → ℝ) (σ : Fin d → Fin n → ℝ) (β : ℝ)
    (hσ : ∀ i j,∑ k,σ i k*σ j k=β⁻¹*(M i j+M j i))
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (x : Fin d → ℝ) :
    coordinateGenerator (fun i y => -(∑ j,M i j*U' y (Pi.single j 1)))
      (fun i j _ => σ i j) f x =
      ∑ i,∑ j,M j i*(-U' x (Pi.single i 1)*fderiv ℝ f x (Pi.single j 1)+
        β⁻¹*fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)) := by
  let H := fun i j => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)
  have hH i j : H i j=H j i := (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq _ _
  have hs : (∑ i,∑ j,H i j*M i j) = ∑ i,∑ j,H i j*M j i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hH j i]
  have hd : (∑ i,fderiv ℝ f x (Pi.single i 1)* -(∑ j,M i j*U' x (Pi.single j 1)))=
      ∑ i,∑ j,M j i*(-U' x (Pi.single i 1)*fderiv ℝ f x (Pi.single j 1)) := by
    simp only [mul_neg,Finset.mul_sum,← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hh : (∑ i,∑ j,H i j*(β⁻¹*(M i j+M j i)))/2=
      ∑ i,∑ j,M j i*(β⁻¹*H i j) := by
    have he : (∑ i,∑ j,H i j*(β⁻¹*(M i j+M j i)))=
        β⁻¹*((∑ i,∑ j,H i j*M i j)+(∑ i,∑ j,H i j*M j i)) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he,hs]
    have he' : (∑ i,∑ j,M j i*(β⁻¹*H i j))=β⁻¹*∑ i,∑ j,H i j*M j i := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he']; ring
  unfold coordinateGenerator
  simp_rw [hσ]
  rw [hd,hh]
  simp only [← Finset.sum_add_distrib,mul_add,H]

end Asakura.Chapter8
