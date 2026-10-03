import Chapter9OUInvariant
import Chapter9Cutoff

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem standard_gaussian_scaled (d : ℕ) (b : ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x => b • x)=
      multivariateGaussian 0 (b^2 • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_map_smul,charFun_stdGaussian,
    charFun_multivariateGaussian (Matrix.PosSemidef.one.smul (sq_nonneg b))]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_zero_right,
    Complex.ofReal_zero,zero_mul,zero_sub,smul_mulVec,one_mulVec,
    dotProduct_smul,smul_eq_mul]
  rw [show (u.ofLp ⬝ᵥ u.ofLp)=‖u‖^2 by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct,pow_two]]
  push_cast
  congr 1
  have hs : ((|b| : ℝ) : ℂ)^2=(b : ℂ)^2 := by exact_mod_cast sq_abs b
  ring_nf
  rw [hs]
  ring

theorem gaussian_affine_law_convolution {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (a b : ℝ) :
    gaussianAffineLaw μ a b=(μ.map (fun x => a • x)) ∗
      multivariateGaussian 0 (b^2 • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  have hh := additive_flow_law μ (stdGaussian (EuclideanSpace ℝ (Fin d)))
    (fun x => a • x) (by fun_prop) (fun y => b • y) (by fun_prop)
  rw [standard_gaussian_scaled] at hh
  exact hh

/-- The Gaussian representation used for the cutoff estimate is the law
of the actual OU stochastic convolution, not an additional assumption. -/
theorem standard_ou_affine_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (t : ℝ) (ht : 0≤t)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    flowLaw μ P (fun x w => Real.exp (-t) • x+
      WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w)))=
      gaussianAffineLaw μ (Real.exp (-t)) (Real.sqrt (1-Real.exp (-2*t))) := by
  let G := fun w => WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w))
  have hG : Measurable G := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    exact measurable_const.mul (Finset.measurable_sum _ (fun j _ =>
      ((hN i j).adapted P B.F _ (half_real_time_finite t)).mono (B.le _) le_rfl))
  have hLaw := vector_ou_convolution_law P B
    ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) N hN hNI t ht
  rw [standard_ou_covariance] at hLaw
  have hv : 0≤1-Real.exp (-2*t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [additive_flow_law μ P (fun x => Real.exp (-t) • x) (by fun_prop) G hG,
    hLaw.map_eq,gaussian_affine_law_convolution,Real.sq_sqrt hv]
end Asakura.Chapter9
