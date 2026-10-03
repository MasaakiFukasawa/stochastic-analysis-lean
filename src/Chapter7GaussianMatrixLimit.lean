import Chapter7EstimatorCovariancePositive
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Matrix Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def estimatorGaussianLaw {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Measure (EuclideanSpace ℝ (Fin d × Fin d)) := multivariateGaussian 0 (estimatorLimitCovariance S)

instance estimatorGaussianLaw_isProbability {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (estimatorGaussianLaw S) :=
  inferInstanceAs (IsProbabilityMeasure (multivariateGaussian 0 (estimatorLimitCovariance S)))

/-- Existence, symmetry, mean and the displayed covariance of the Gaussian
matrix. Degenerate covariance matrices are included. -/
theorem estimator_gaussian_matrix {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (S : Matrix (Fin d) (Fin d) ℝ) :
    (∀ p,(∫ g,g p ∂estimatorGaussianLaw S)=0) ∧
    (∀ p q,cov[(fun g => g p),(fun g => g q);estimatorGaussianLaw S]=estimatorLimitCovariance S p q) ∧
    (∀ᵐ g ∂estimatorGaussianLaw S,∀ i j,g (i,j)=g (j,i)) := by
  let μ := estimatorGaussianLaw S
  letI : IsGaussian μ := inferInstanceAs (IsGaussian (multivariateGaussian 0 (estimatorLimitCovariance S)))
  have hps := estimator_covariance_posSemidef P B S
  have hlp p : MemLp (fun g : EuclideanSpace ℝ (Fin d × Fin d) => g p) 2 μ := by
    simpa only [Function.comp_def,id_eq,EuclideanSpace.coe_proj] using
      (IsGaussian.hasGaussianLaw_id (μ := μ) |>.map (EuclideanSpace.proj p)).memLp_two
  have hmean p : (∫ g,g p ∂μ)=0 := by
    have he := (EuclideanSpace.proj p).integral_comp_id_comm (IsGaussian.integrable_id (μ := μ))
    simpa only [μ,estimatorGaussianLaw,integral_id_multivariateGaussian,map_zero,EuclideanSpace.coe_proj] using he
  have hcov p q : cov[(fun g => g p),(fun g => g q);μ]=estimatorLimitCovariance S p q :=
    covariance_eval_multivariateGaussian hps p q
  refine ⟨hmean,hcov,?_⟩
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hd : MemLp (fun g => g (i,j)-g (j,i)) 2 μ := (hlp (i,j)).sub (hlp (j,i))
  have hv : Var[(fun g => g (i,j)-g (j,i));μ]=0 := by
    rw [variance_fun_sub (hlp (i,j)) (hlp (j,i))]
    rw [← covariance_self (hlp (i,j)).aestronglyMeasurable.aemeasurable,
      ← covariance_self (hlp (j,i)).aestronglyMeasurable.aemeasurable,hcov,hcov,hcov]
    dsimp only [estimatorLimitCovariance]
    ring
  have he : (∫ g,g (i,j)-g (j,i) ∂μ)=0 := by
    rw [integral_sub ((hlp _).integrable (by norm_num)) ((hlp _).integrable (by norm_num)),hmean,hmean,sub_self]
  have hz := ae_eq_integral_of_variance_eq_zero hd hv
  filter_upwards [hz] with g hg
  rw [he] at hg
  exact sub_eq_zero.mp hg

end Asakura.Chapter7
