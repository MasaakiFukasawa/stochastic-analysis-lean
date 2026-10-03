import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

/-- Every scalar projection of the canonical Gaussian has the quadratic
variance used by the martingale proof. -/
theorem multivariate_gaussian_projection_law {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (v : EuclideanSpace ℝ ι) :
    HasLaw (fun x : EuclideanSpace ℝ ι => ⟪x,v⟫)
      (gaussianReal 0 (v ⬝ᵥ S *ᵥ v).toNNReal) (multivariateGaussian 0 S) := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ v
  have hL : (L : _ → ℝ) = fun x => ⟪x,v⟫ := by
    funext x
    exact real_inner_comm x v
  have hv : Var[L;μ] = v ⬝ᵥ S *ᵥ v := by
    change Var[(fun x => ⟪v,x⟫);μ] = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id v]
    exact covarianceBilin_multivariateGaussian hS v v
  have hm : (∫ x,L x ∂μ)=0 := by
    have hh := L.integral_comp_id_comm (IsGaussian.integrable_id (μ := μ))
    simpa [μ] using hh
  refine ⟨by rw [← hL]; exact L.continuous.measurable.aemeasurable,?_⟩
  rw [← hL,IsGaussian.map_eq_gaussianReal,hm,hv]

end Asakura.Chapter8
