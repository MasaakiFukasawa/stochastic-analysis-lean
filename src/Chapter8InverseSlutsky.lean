import Chapter8MatrixProbability
import Chapter8LongTimeMatrixBracketCLT

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The total matrix inverse is Borel measurable, although continuous only
at invertible matrices. -/
theorem matrix_inverse_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℝ => A⁻¹) := by
  have hh : Measurable (fun A : Matrix ι ι ℝ => A.det⁻¹ • A.adjugate) :=
    continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable
  simpa only [Matrix.inv_def,Ring.inverse_eq_inv] using hh

/-- Slutsky's step for the normalised likelihood equation: entrywise
information convergence and the score CLT yield the inverse-information
transform of the limiting Gaussian. -/
theorem inverse_information_slutsky {Ω Γ ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Γ] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (Z : Γ → EuclideanSpace ℝ ι)
    (J : ℕ → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) (hS : S.det ≠ 0)
    (hX : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hm : ∀ n, Measurable (J n))
    (hJ : ∀ i j,TendstoInMeasure P (fun n ω => J n ω i j) atTop (fun _ => S i j)) :
    TendstoInDistribution (fun n ω => Matrix.toEuclideanCLM (𝕜 := ℝ) (J n ω)⁻¹ (X n ω)) atTop
      (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ (Z z)) (fun _ => P) Q := by
  have hi := probability_matrix_inverse P atTop J S hS (probability_matrix_of_entries P atTop J S hJ)
  have hc : Continuous (fun p : EuclideanSpace ℝ ι × Matrix ι ι ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) p.2 p.1) := by
    change Continuous (fun p : EuclideanSpace ℝ ι × Matrix ι ι ℝ =>
      WithLp.toLp 2 (p.2 *ᵥ p.1))
    apply (show Continuous (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop).comp
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    have h1 : Continuous (fun p : EuclideanSpace ℝ ι × Matrix ι ι ℝ => p.2 i j) := by fun_prop
    have h2 : Continuous (fun p : EuclideanSpace ℝ ι × Matrix ι ι ℝ => p.1 j) :=
      (EuclideanSpace.proj j).continuous.comp continuous_fst
    exact h1.mul h2
  exact hX.continuous_comp_prodMk_of_tendstoInMeasure_const hc hi
    (fun n => (matrix_inverse_measurable.comp (hm n)).aemeasurable)

end Asakura.Chapter8
