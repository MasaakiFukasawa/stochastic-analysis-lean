import Chapter8BoundedExpectationDerivative
import Mathlib.Analysis.Calculus.ContDiff.Defs

open MeasureTheory Set Filter
namespace Asakura.Chapter8
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Two justified differentiations under expectation and continuity of
the second derivative. Actual pathwise derivatives and deterministic
bounds give C2 regularity of the expectation. -/
theorem bounded_expectation_C2 {E F Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : E → Ω → F) (D : E → Ω → E →L[ℝ] F)
    (D₂ : E → Ω → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ x,AEStronglyMeasurable (f x) P)
    (hDm : ∀ x,AEStronglyMeasurable (D x) P)
    (hD₂m : ∀ x,AEStronglyMeasurable (D₂ x) P)
    (B₀ B₁ B₂ : ℝ) (hfb : ∀ x,∀ᵐ ω ∂P,‖f x ω‖ ≤ B₀)
    (hDb : ∀ᵐ ω ∂P,∀ x,‖D x ω‖ ≤ B₁)
    (hD₂b : ∀ᵐ ω ∂P,∀ x,‖D₂ x ω‖ ≤ B₂)
    (hD : ∀ᵐ ω ∂P,∀ x,HasFDerivAt (fun z => f z ω) (D x ω) x)
    (hD₂ : ∀ᵐ ω ∂P,∀ x,HasFDerivAt (fun z => D z ω) (D₂ x ω) x)
    (hD₂c : ∀ᵐ ω ∂P,Continuous (fun x => D₂ x ω)) :
    ContDiff ℝ 2 (fun x => ∫ ω,f x ω ∂P) ∧
      (∀ x,HasFDerivAt (fun z => ∫ ω,f z ω ∂P) (∫ ω,D x ω ∂P) x) ∧
      (∀ x,HasFDerivAt (fun z => ∫ ω,D z ω ∂P) (∫ ω,D₂ x ω ∂P) x) ∧
      (∀ x,‖fderiv ℝ (fun z => ∫ ω,f z ω ∂P) x‖ ≤ B₁) ∧
      ∀ x,‖fderiv ℝ (fderiv ℝ (fun z => ∫ ω,f z ω ∂P)) x‖ ≤ B₂ := by
  have h1 := bounded_expectation_derivative P f D hf hDm B₀ B₁ hfb hDb hD
  have h2 := bounded_expectation_derivative P D D₂ hDm hD₂m B₁ B₂
    (fun x => hDb.mono (fun _ h => h x)) hD₂b hD₂
  have hc : Continuous (fun x => ∫ ω,D₂ x ω ∂P) :=
    continuous_of_dominated hD₂m (fun x => hD₂b.mono (fun _ h => h x)) (integrable_const B₂) hD₂c
  refine ⟨?_,h1,h2,?_,?_⟩
  · apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    refine ⟨fun x => ∫ ω,D x ω ∂P,?_,h1⟩
    exact contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => ∫ ω,D₂ x ω ∂P,hc,h2⟩
  · intro x
    rw [(h1 x).fderiv]
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (hDb.mono (fun _ h => h x))
  · intro x
    have he : fderiv ℝ (fun z => ∫ ω,f z ω ∂P)=(fun z => ∫ ω,D z ω ∂P) :=
      funext (fun z => (h1 z).fderiv)
    rw [he,(h2 x).fderiv]
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (hD₂b.mono (fun _ h => h x))

end Asakura.Chapter8
