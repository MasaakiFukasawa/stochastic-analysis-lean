import Chapter8GaussianProjection

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace Asakura.Chapter8

/-- Exact Gaussian laws of all projections identify a vector law without
requiring a positive definite covariance. -/
theorem gaussian_law_of_projections {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : AEMeasurable X P)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hp : ∀ v : EuclideanSpace ℝ (Fin d),HasLaw (fun w => ⟪X w,v⟫)
      (gaussianReal 0 (v ⬝ᵥ S *ᵥ v).toNNReal) P) :
    HasLaw X (multivariateGaussian 0 S) P := by
  refine ⟨hX,?_⟩
  apply Measure.ext_of_charFun
  funext v
  rw [charFun_map_eq_charFun_map_inner_one hX v,(hp v).map_eq,
    ←(multivariate_gaussian_projection_law S hS v).map_eq]
  have hh := charFun_map_eq_charFun_map_inner_one
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S)
    (Y := id) measurable_id.aemeasurable v
  simpa only [Measure.map_id,id_eq] using hh.symm

end Asakura.Chapter8
