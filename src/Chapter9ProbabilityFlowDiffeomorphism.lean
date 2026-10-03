import Chapter9ProbabilityFlowC1
import Chapter9FlowDiffeomorphism

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The actual probability flow has a global differentiable inverse,
constructed by solving the reversed ordinary differential equation. -/
theorem probability_flow_diffeomorphism {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (ε T : ℝ) (hε : 0<ε) (hT : 0≤T) :
    let F := fun s => ouProbabilityVelocity μ d (ε+max s 0)
    ∃ e : E ≃ₜ E,Differentiable ℝ e ∧ Differentiable ℝ e.symm ∧
      ∀ x,∃ X : ℝ → E,Continuous X ∧ X T=e x ∧
        (∀ s∈Icc 0 T,X s=x+∫ r in 0..s,F r (X r)) ∧
        ∃ J : ℝ → E →L[ℝ] E,Continuous J ∧
          (∀ t∈Icc 0 T,∀ h,J t h=h+∫ r in 0..t,(fderiv ℝ (F r) (X r)) (J r h)) ∧
          HasFDerivAt e (J T) x := by
  obtain ⟨K,hFc,hK⟩ := ou_clamped_velocity_regularity μ d R hR hb ε hε
  obtain ⟨hd,hDc⟩ := ou_clamped_velocity_c1 μ d R hb ε hε
  exact time_dependent_flow_diffeomorphism _ _ hFc hDc (fun s y => (hd s y).hasFDerivAt) K hK T hT
end Asakura.Chapter9
