import Chapter8WhiteningGaussian
import Chapter8LikelihoodCLTAssembly

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology MatrixOrder Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The self-normalisation step uses continuity of the square root on
positive semidefinite information matrices and the already proved MLE CLT. -/
theorem self_normalised_likelihood_clt {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → EuclideanSpace ℝ ι)
    (J : ℕ → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hY : TendstoInDistribution Y atTop id (fun _ => P) (multivariateGaussian 0 S⁻¹))
    (hmJ : ∀ n,Measurable (J n)) (hJpos : ∀ n ω,(J n ω).PosSemidef)
    (hJ : ∀ i j,TendstoInMeasure P (fun n ω => J n ω i j) atTop (fun _ => S i j)) :
    TendstoInDistribution (fun n ω => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (J n ω)) (Y n ω))
      atTop id (fun _ => P) (multivariateGaussian 0 1) := by
  have hsqrt := probability_information_square_root P atTop J S hS.posSemidef hJpos
    (probability_matrix_of_entries P atTop J S hJ)
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

  have hd := hY.continuous_comp_prodMk_of_tendstoInMeasure_const hc hsqrt
    (fun n => (matrix_sqrt_measurable.comp (hmJ n)).aemeasurable)
  refine ⟨hd.forall_aemeasurable,measurable_id.aemeasurable,?_⟩
  have hp : (⟨(multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)),inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ ι)) =
      ⟨(multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map id,inferInstance⟩ := by
    apply Subtype.ext
    change (multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) =
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map id
    rw [Measure.map_id]
    exact whitening_gaussian_law S hS
  rw [← hp]
  exact hd.tendsto

end Asakura.Chapter8
