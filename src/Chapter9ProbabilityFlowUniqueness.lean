import Chapter9ProbabilityFlowExistence

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter9
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Uniqueness is for the actual Gaussian-mixture velocity on the entire
positive-time strip, not for a velocity supplied as an extra assumption. -/
theorem probability_flow_unique {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (R : ℝ) (hR : 0≤R) (hb : ∀ᵐ x ∂μ,‖x‖≤R)
    (ε H : ℝ) (hε : 0<ε) (hH : 0≤H) (x : E)
    (X Y : ℝ → E) (hcX : Continuous X) (hcY : Continuous Y)
    (hX : ∀ s∈Icc 0 H,X s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (X r))
    (hY : ∀ s∈Icc 0 H,Y s=x+∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (Y r)) :
    ∀ s∈Icc 0 H,X s=Y s := by
  let F := fun s y => ouProbabilityVelocity μ d (ε+max s 0) y
  obtain ⟨K,hFc,hFK⟩ := ou_clamped_velocity_regularity μ d R hR hb ε hε
  have he (Z : ℝ → E) s (hs : 0≤s) :
      (∫ r in 0..s,F r (Z r))=∫ r in 0..s,ouProbabilityVelocity μ d (ε+r) (Z r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp [F]
    rw [max_eq_left ((uIcc_of_le hs ▸ hr).1)]
  have h := time_dependent_initial_stability F K hFc hFK X Y (fun _ => 0) hcX hcY x x H hH
    (fun s hs => by simpa only [he X s hs.1,add_zero] using hX s hs)
    (fun s hs => by simpa only [he Y s hs.1,add_zero] using hY s hs)
  intro s hs
  have hh := h s hs
  simp only [sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
end Asakura.Chapter9
