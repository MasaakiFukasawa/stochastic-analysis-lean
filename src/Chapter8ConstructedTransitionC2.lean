import Chapter8SmoothFlowExpectation
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct a jointly measurable additive flow and prove C2 regularity
of its actual transition expectations from the drift and observable
hypotheses, rather than assuming a smooth semigroup. -/
theorem constructed_transition_C2 {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (b : E → E) (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hDC : LipschitzWith C D)
    (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ)) (T : ℝ) (hT : 0 ≤ T)
    (V : Ω → C(Icc (0:ℝ) T,E)) (hV : Measurable V)
    (f : E → ℝ) (Df : E → E →L[ℝ] ℝ) (D₂f : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ∀ z,HasFDerivAt f (Df z) z) (hDf : ∀ z,HasFDerivAt Df (D₂f z) z)
    (hcD₂f : Continuous D₂f) (B₀ B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hfb : ∀ z,‖f z‖ ≤ B₀) (hDfb : ∀ z,‖Df z‖ ≤ B₁) (hD₂fb : ∀ z,‖D₂f z‖ ≤ B₂) :
    ∃ S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E),Continuous S ∧
      (∀ p t,S p t=p.1+(∫ s in 0..t.val,b (S p (projIcc 0 T hT s)))+p.2 t) ∧
      ∀ t : Icc (0:ℝ) T,ContDiff ℝ 2 (fun x => ∫ ω,f (S (x,V ω) t) ∂P) := by
  obtain ⟨S,J,K,hSc,hJc,hKc,hS,hSJ,hJK,hJb,hKb⟩ :=
    canonical_smooth_additive_flow b D D₂ hD hD₂ hcD₂ C L hDC hL hDb T hT
  refine ⟨S,hSc,hS,?_⟩
  intro t
  exact (smooth_flow_expectation_C2 P V hV (fun p => S p t) (fun p => J p t) (fun p => K p t)
    ((continuous_eval_const t).comp hSc) ((continuous_eval_const t).comp hJc) ((continuous_eval_const t).comp hKc)
    (fun x w => hSJ x w t) (fun x w => hJK x w t)
    (Real.exp (((L:ℝ)+1)*T)) ((C:ℝ)*Real.exp (((L:ℝ)+1)*T)^2*T*Real.exp ((L:ℝ)*T))
    (Real.exp_pos _).le (by positivity) (fun p => hJb p t) (fun p => hKb p t)
    f Df D₂f hf hDf hcD₂f B₀ B₁ B₂ hB₁ hB₂ hfb hDfb hD₂fb).1

end Asakura.Chapter8
