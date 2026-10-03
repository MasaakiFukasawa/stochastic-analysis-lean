import Chapter8InverseGaussian
import Chapter8NonsingularEvent

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology Matrix.Norms.Elementwise
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The likelihood-equation step of the MLE proof, including the arbitrary
convention on singular information. The score limit and information limit
are the exact two inputs to be supplied by the preceding SDE arguments. -/
theorem likelihood_clt_assembly {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℕ → Ω → EuclideanSpace ℝ ι)
    (J : ℕ → Ω → Matrix ι ι ℝ) (S : Matrix ι ι ℝ) (hS : S.PosDef)
    (hX : TendstoInDistribution X atTop id (fun _ => P) (multivariateGaussian 0 S))
    (hmJ : ∀ n,Measurable (J n)) (hmY : ∀ n,AEMeasurable (Y n) P)
    (hJ : ∀ i j,TendstoInMeasure P (fun n ω => J n ω i j) atTop (fun _ => S i j))
    (he : ∀ n ω,(J n ω).det ≠ 0 →
      Y n ω=Matrix.toEuclideanCLM (𝕜 := ℝ) (J n ω)⁻¹ (X n ω)) :
    TendstoInDistribution Y atTop id (fun _ => P) (multivariateGaussian 0 S⁻¹) := by
  have hinv := inverse_information_slutsky P (multivariateGaussian 0 S) X id J S
    hS.det_pos.ne' hX hmJ hJ
  have hdist := distribution_of_nonsingular_formula P (multivariateGaussian 0 S)
    (fun n ω => Matrix.toEuclideanCLM (𝕜 := ℝ) (J n ω)⁻¹ (X n ω)) Y
    (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z) hinv hmY J S hS.det_pos.ne'
    (probability_matrix_of_entries P atTop J S hJ) he
  refine ⟨hdist.forall_aemeasurable,measurable_id.aemeasurable,?_⟩
  have hmap := inverse_gaussian_law S hS
  have hp : (⟨(multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹),inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ ι)) =
      ⟨(multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹).map id,inferInstance⟩ := by
    apply Subtype.ext
    change (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) =
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S⁻¹).map id
    rw [Measure.map_id]
    exact hmap
  rw [← hp]
  exact hdist.tendsto

end Asakura.Chapter8
