import Chapter8OUGramCovariance

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8

/-- Any direction orthogonal to the noise has zero variance under the
invariant law; that law is concentrated on the corresponding hyperplane. -/
theorem ou_degenerate_hyperplane {d n : ℕ} (σ : Matrix (Fin d) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hzero : ∀ j,∑ i,v i*σ i j=0) :
    ∀ᵐ x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) ((1/2:ℝ) • (σ*σᵀ)),⟪x,v⟫=0 := by
  have hl := multivariate_gaussian_projection_law _ (ou_gram_covariance σ).1 v
  rw [(ou_gram_covariance σ).2 v] at hl
  simp only [hzero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,zero_div,
    Real.toNNReal_zero,gaussianReal_zero_var] at hl
  exact hl.ae_eq_of_dirac

theorem nonzero_direction_hyperplane_proper {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d)) (hv : v≠0) : {x | inner ℝ x v=0}≠Set.univ := by
  intro h
  have hh : v∈{x | inner ℝ x v=0} := by rw [h]; trivial
  have he : inner ℝ v v=0 := hh
  exact hv (inner_self_eq_zero.mp he)

theorem ou_zero_noise_invariant (d n : ℕ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      ((1/2:ℝ) • ((0 : Matrix (Fin d) (Fin n) ℝ)*0ᵀ))=Measure.dirac 0 := by
  simp [multivariateGaussian]

end Asakura.Chapter8
