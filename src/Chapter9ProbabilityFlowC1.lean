import Chapter9ProbabilityFlowExistence
import Chapter9ScoreDerivativeContinuity
import Chapter9TimeDependentFlowC1

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem ou_clamped_velocity_c1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (R : ℝ) (hb : ∀ᵐ x ∂μ,‖x‖≤R) (ε : ℝ) (hε : 0<ε) :
    let F := fun s => ouProbabilityVelocity μ d (ε+max s 0)
    (∀ s x,DifferentiableAt ℝ (F s) x) ∧
      Continuous (fun z : ℝ × E => fderiv ℝ (F z.1) z.2) := by
  let τ := fun s : ℝ => ε+max s 0
  have hτ : Continuous τ := by dsimp [τ]; fun_prop
  have hτε s : ε≤τ s := by dsimp [τ]; linarith [le_max_right s (0:ℝ)]
  have hτp s : 0<τ s := hε.trans_le (hτε s)
  let v := fun s => 1-Real.exp (-2*τ s)
  let a := fun s => Real.exp (-τ s)
  let c := fun s => Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v s))
  have hvp s : 0<v s := ou_variance_positive _ (hτp s)
  have hv : Continuous v := by dsimp [v]; fun_prop
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hc : Continuous c := by
    dsimp [c]
    fun_prop (disch := intro s; exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (hvp _).ne')
  let G := fun s y => (∫ x,radialKernel (c s) (a s) (v s) x y ∂μ)⁻¹ •
    (∫ x,(-radialKernel (c s) (a s) (v s) x y/v s) • (y-a s • x) ∂μ)
  have hG s y : DifferentiableAt ℝ (G s) y :=
    (radial_score_fderiv μ (c s) (a s) (v s) (Real.exp_pos _) (hvp s) y).differentiableAt
  have hD := compact_radial_score_derivative_continuous μ R hb c a v hc ha hv
    (fun _ => Real.exp_pos _) hvp
  have hd s y : HasFDerivAt (ouProbabilityVelocity μ d (τ s))
      (-ContinuousLinearMap.id ℝ E-fderiv ℝ (G s) y) y :=
    (hasFDerivAt_id y).neg.sub (hG s y).hasFDerivAt
  refine ⟨fun s x => (hd s x).differentiableAt,?_⟩
  have he (z : ℝ × E) := (hd z.1 z.2).fderiv
  change Continuous (fun z : ℝ × E => fderiv ℝ (ouProbabilityVelocity μ d (τ z.1)) z.2)
  simp_rw [he]
  exact continuous_const.sub hD

/-- The probability-flow solution is constructed together with its actual
initial-state derivative and variational integral equation. -/
theorem probability_flow_initial_derivative_exists {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (ε T : ℝ) (hε : 0<ε) (hT : 0≤T) :
    let F := fun s => ouProbabilityVelocity μ d (ε+max s 0)
    ∃ X : E → ℝ → E,
      (∀ x,Continuous (X x)) ∧
      (∀ x t,t∈Icc 0 T → X x t=x+∫ s in 0..t,F s (X x s)) ∧
      ∀ x,∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
        (∀ t,t∈Icc 0 T → ∀ h,J t h=h+∫ s in 0..t,(fderiv ℝ (F s) (X x s)) (J s h)) ∧
        ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J t) x := by
  obtain ⟨K,hFc,hK⟩ := ou_clamped_velocity_regularity μ d R hR hb ε hε
  obtain ⟨hd,hDc⟩ := ou_clamped_velocity_c1 μ d R hb ε hε
  exact time_dependent_flow_c1_exists _ _ hFc hDc (fun s y => (hd s y).hasFDerivAt) K hK T hT
end Asakura.Chapter9
