import Chapter8CenteredMoment

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Asakura.Chapter8
open Asakura.FullAudit

/-- The exact covariance constant L_f² m₂ exp(-κt) is obtained from the
synchronous coupling; no covariance estimate is assumed. -/
theorem stationary_transition_covariance {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (π : Measure E) [IsProbabilityMeasure π]
    (hπ : MemLp (fun x : E => x) 2 π)
    (X : E → Ω → E) (hX : ∀ x, MemLp (X x) 2 P)
    (f : E → ℝ) (L : ℝ≥0) (hf : LipschitzWith L f) (κ t : ℝ)
    (hLip : ∀ x y, ∀ᵐ ω ∂P, ‖X x ω-X y ω‖ ≤ Real.exp (-κ*t)*‖x-y‖) :
    |cov[f,(fun x => ∫ ω,f (X x ω) ∂P);π]| ≤
      (L:ℝ)^2*(∫ x, ‖x‖^2 ∂π)*Real.exp (-κ*t) := by
  let a : ℝ≥0 := ⟨Real.exp (-κ*t),(Real.exp_pos _).le⟩
  have hg := lipschitz_transition_from_coupling P X hX f L a hf hLip
  have hf2 := lipschitz_observable_memLp π (fun x => x) hπ f L hf
  have hg2 := lipschitz_observable_memLp π (fun x => x) hπ
    (fun x => ∫ ω,f (X x ω) ∂P) (L*a) hg
  have hh := lipschitz_covariance_decay π hπ f (fun x => ∫ ω,f (X x ω) ∂P) L κ t hf hg hf2 hg2
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (centered_second_moment_le π hπ) (sq_nonneg _))
    (Real.exp_pos _).le

end Asakura.Chapter8
