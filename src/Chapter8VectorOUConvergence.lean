import Chapter8VectorOUTransition
import Chapter8AdditiveFlowLaw

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace Asakura.Chapter8
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The Gaussian law of the actual OU integral implies invariance and
geometric convergence for every constant diffusion matrix. -/
theorem vector_ou_invariance_convergence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d n : ℕ} (B : BrownianSystem P n)
    (σ : Matrix (Fin d) (Fin n) ℝ)
    (N : Fin d → Fin n → HalfClosedTime → Ω → ℝ)
    (hN : ∀ i j,LocalMProcessWitness P B.F (N i j))
    (hNI : ∀ i j,ItoCovarianceFormula P B.F (B.W j) (fun z => σ i j*Real.exp z.2) (N i j))
    (t : ℝ) (ht : 0≤t) :
    let π := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) ((1/2:ℝ) • (σ*σᵀ))
    let F := fun x w => Real.exp (-t) • x+
      WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w))
    flowLaw π P F=π ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))),IsProbabilityMeasure μ → MemLp (fun z => z) 2 μ →
        transportDistance (flowLaw μ P F) π≤Real.exp (-t)*transportDistance μ π := by
  dsimp only
  let S := (1/2:ℝ) • (σ*σᵀ)
  let π := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S
  let G := fun w => WithLp.toLp 2 (fun i => Real.exp (-t)*(∑ j,N i j (realTimeClamp t) w))
  let F := fun x w => Real.exp (-t) • x+G w
  have hm : Measurable G := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_lambda
    intro i
    exact measurable_const.mul (Finset.measurable_sum _ (fun j _ =>
      ((hN i j).adapted P B.F _ (half_real_time_finite t)).mono (B.le _) le_rfl))
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (fun z : EuclideanSpace ℝ (Fin d) × Ω => Real.exp (-t) • z.1+G z.2)
    exact (measurable_fst.const_smul (Real.exp (-t))).add (hm.comp measurable_snd)
  have hLaw := vector_ou_convolution_law P B σ N hN hNI t ht
  have hi : flowLaw π P F=π := by
    rw [additive_flow_law π P (fun x => Real.exp (-t) • x) (by fun_prop) G hm,hLaw.map_eq]
    exact vector_ou_gaussian_invariant_time S (ou_gram_covariance σ).1 t ht
  refine ⟨hi,?_⟩
  intro μ hμp hμ
  letI := hμp
  have hπ : MemLp (fun x => x) 2 π := IsGaussian.memLp_two_id
  haveI := quadratic_coupling_nonempty μ π hμ hπ
  have hc := shared_noise_transport_contraction μ π P F hF (Real.exp (-t)) (Real.exp_pos _)
    (fun x y => ae_of_all _ fun w => by
      change ‖(Real.exp (-t) • x+G w)-(Real.exp (-t) • y+G w)‖≤Real.exp (-t)*‖x-y‖
      rw [add_sub_add_right_eq_sub,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)])
  rwa [hi] at hc

end Asakura.Chapter8
