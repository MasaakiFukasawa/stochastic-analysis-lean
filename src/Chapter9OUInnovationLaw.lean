import Chapter9IncrementGaussian
import Chapter9OUIncrementVariance
import Chapter8VectorOUConstructed
import Chapter8DeterministicVectorItoLaw
import Chapter8GaussianFromProjections
import Chapter8OUGramCovariance

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
namespace Asakura.Chapter9
open Asakura.Chapter8 Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The actual OU stochastic convolution has its full multivariate
Gaussian law, with covariance (1-exp(-2t)) Sigma Sigma-transpose / 2. -/
theorem vector_ou_innovation_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (σ : Matrix (Fin d) (Fin n) ℝ)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => σ i j*Real.exp z.2) (N i j))
    (t s : ℝ) (ht : 0≤t) (hs : s∈Set.Icc 0 t) :
    HasLaw (fun w => WithLp.toLp 2 (fun i => Real.exp (-t)*(Finset.sum Finset.univ (fun j : Fin n => N i j (realTimeClamp t) w-N i j (realTimeClamp s) w))))
      (multivariateGaussian 0 ((1-Real.exp (-2*(t-s))) • ((1/2:ℝ) • (σ*σᵀ)))) P := by
  let S := (1/2:ℝ) • (σ*σᵀ)
  let V := (1-Real.exp (-2*(t-s))) • S
  have hS : S.PosSemidef := (ou_gram_covariance σ).1
  have ha : 0≤1-Real.exp (-2*(t-s)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith [hs.2]))
  have hV : V.PosSemidef := hS.smul ha
  have hm : Measurable (fun w => WithLp.toLp 2 (fun i => Real.exp (-t)*(Finset.sum Finset.univ (fun j : Fin n => N i j (realTimeClamp t) w-N i j (realTimeClamp s) w)))) := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    exact measurable_const.mul (Finset.measurable_sum _ (fun j _ =>
      (((hN i j).adapted P B.F _ (half_real_time_finite t)).mono (B.le _) le_rfl).sub
        (((hN i j).adapted P B.F _ (half_real_time_finite s)).mono (B.le _) le_rfl)))
  apply gaussian_law_of_projections P _ hm.aemeasurable V hV
  intro v
  have hl := vector_ito_increment_projection_law P B (fun i j r => σ i j*Real.exp r)
    (fun i j => by fun_prop) N hN hNI v t s ht hs
  have hh := gaussianReal_const_mul hl (Real.exp (-t))
  have hnon : 0≤v ⬝ᵥ V *ᵥ v := by simpa only [star_trivial] using hV.dotProduct_mulVec_nonneg v
  have hv : (⟨Real.exp (-t)^2,sq_nonneg _⟩ : ℝ≥0)*
      ⟨∫ r in s..t,∑ j,(∑ i,v i*(σ i j*Real.exp r))^2,
        intervalIntegral.integral_nonneg_of_forall hs.2 (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))⟩=
      (v ⬝ᵥ V *ᵥ v).toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ hnon]
    change Real.exp (-t)^2*(∫ r in s..t,∑ j,(∑ i,v i*(σ i j*Real.exp r))^2)=v ⬝ᵥ V *ᵥ v
    rw [ou_increment_projection_variance]
    simp only [V,S,smul_mulVec,dotProduct_smul,smul_eq_mul]
  rw [mul_zero] at hh
  dsimp only [NNReal.mk] at hh
  rw [hv] at hh
  apply hh.congr
  apply ae_of_all
  intro w
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,WithLp.ofLp_toLp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Asakura.Chapter9
