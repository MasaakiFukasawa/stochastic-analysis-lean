import Chapter8VectorOUConvergence
import Chapter9GaussianMoments

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem standard_ou_covariance (d : ℕ) :
    (1/2:ℝ) • (((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ))*
      ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ)=1 := by
  have hs : Real.sqrt 2*Real.sqrt 2=2 := Real.mul_self_sqrt (by norm_num)
  simp only [transpose_smul,transpose_one,Matrix.smul_mul,Matrix.mul_smul,one_mul,smul_smul]
  rw [hs]
  norm_num

/-- Apply the constructed OU stochastic integral result with precisely
the diffusion matrix of Chapter 9. Its invariant covariance is the identity. -/
theorem standard_ou_invariance_convergence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (t : ℝ) (ht : 0≤t) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
    let F := fun x w => Real.exp (-t) • x+
      WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w))
    flowLaw γ P F=γ ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))),IsProbabilityMeasure μ → MemLp (fun z => z) 2 μ →
        transportDistance (flowLaw μ P F) γ≤Real.exp (-t)*transportDistance μ γ := by
  have hh := vector_ou_invariance_convergence P B
    ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) N hN hNI t ht
  dsimp only at hh ⊢
  rw [standard_ou_covariance,multivariateGaussian_zero_one] at hh
  exact hh

/-- The explicit normal-approximation estimate follows from the actual
OU contraction and the independent standard-Gaussian coupling. -/
theorem standard_ou_normal_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (t : ℝ) (ht : 0≤t)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z => z) 2 μ) :
    let F := fun x w => Real.exp (-t) • x+
      WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w))
    transportDistance (flowLaw μ P F) (stdGaussian (EuclideanSpace ℝ (Fin d))) ≤
      Real.exp (-t)*Real.sqrt ((∫ x,‖x‖^2 ∂μ)+(d:ℝ)) := by
  exact ((standard_ou_invariance_convergence P B N hN hNI t ht).2 μ inferInstance hμ).trans
    (mul_le_mul_of_nonneg_left (distance_to_standard_gaussian μ hμ) (Real.exp_pos _).le)

theorem standard_ou_unique_invariant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (N : Fin d → Fin d → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j)
      (fun z => ((Real.sqrt 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) i j*Real.exp z.2) (N i j))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun z => z) 2 μ)
    (hinv : flowLaw μ P (fun x w => Real.exp (-1) • x+
      WithLp.toLp 2 (fun i => Real.exp (-1)*(∑ j,N i j (realTimeClamp 1) w)))=μ) :
    μ=stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin d))
  haveI : Nonempty (QuadraticCoupling μ γ) :=
    quadratic_coupling_nonempty μ γ hμ IsGaussian.memLp_two_id
  have hh := (standard_ou_invariance_convergence P B N hN hNI 1 (by norm_num)).2 μ inferInstance hμ
  rw [hinv] at hh
  have he : Real.exp (-1)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hn : 0≤transportDistance μ γ := Real.sqrt_nonneg _
  have hz : transportDistance μ γ=0 := by nlinarith
  apply zero_transport_measures_equal μ γ
  have hs := Real.sq_sqrt (transport_energy_nonnegative μ γ)
  change transportDistance μ γ ^2=transportEnergy μ γ at hs
  rw [hz] at hs
  simpa using hs.symm
end Asakura.Chapter9
