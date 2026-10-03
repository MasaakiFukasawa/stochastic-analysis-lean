import Chapter7GaussianMatrixLimit
import Chapter7CovarianceContraction

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.Chapter4
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

lemma gaussian_matrix_linear_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (H S : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose=H) :
    HasLaw (fun g : EuclideanSpace ℝ (Fin d × Fin d) => ∑ i,∑ j,H i j*g (i,j))
      (gaussianReal 0 (2*(∑ i,∑ j,(S.transpose*H*S) i j^2)).toNNReal) (estimatorGaussianLaw S) := by
  let μ := estimatorGaussianLaw S
  letI : IsGaussian μ := inferInstanceAs (IsGaussian (multivariateGaussian 0 (estimatorLimitCovariance S)))
  let v : EuclideanSpace ℝ (Fin d × Fin d) := WithLp.toLp 2 (fun p => H p.1 p.2)
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d × Fin d)) := innerSL ℝ v
  have hL : (L : _ → ℝ)=(fun g => ∑ i,∑ j,H i j*g (i,j)) := by
    funext g
    change inner ℝ v g = _
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,v,WithLp.ofLp_toLp,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hv : Var[L;μ]=2*(∑ i,∑ j,(S.transpose*H*S) i j^2) := by
    change Var[(fun g => inner ℝ v g);μ]=_
    rw [← covarianceBilin_self IsGaussian.memLp_two_id v]
    dsimp only [μ,estimatorGaussianLaw]
    rw [
      covarianceBilin_multivariateGaussian (estimator_covariance_posSemidef P B S)]
    exact estimator_covariance_contraction H S hH
  have hm : (∫ g,L g ∂μ)=0 := by
    have he := L.integral_comp_id_comm (IsGaussian.integrable_id (μ := μ))
    simpa only [μ,estimatorGaussianLaw,integral_id_multivariateGaussian,map_zero] using he
  refine ⟨by rw [← hL]; exact L.continuous.measurable.aemeasurable,?_⟩
  rw [← hL,IsGaussian.map_eq_gaussianReal,hm,hv]

end Asakura.Chapter7
