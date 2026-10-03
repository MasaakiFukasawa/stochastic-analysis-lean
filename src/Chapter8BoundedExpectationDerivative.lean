import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter8
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

/-- A deterministic bound on the actual derivatives justifies taking a
first derivative inside an expectation. This will be used twice. -/
theorem bounded_expectation_derivative {E F Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : E → Ω → F) (D : E → Ω → E →L[ℝ] F)
    (hf : ∀ x,AEStronglyMeasurable (f x) P)
    (hDm : ∀ x,AEStronglyMeasurable (D x) P)
    (B C : ℝ) (hfb : ∀ x,∀ᵐ ω ∂P,‖f x ω‖ ≤ B)
    (hDb : ∀ᵐ ω ∂P,∀ x,‖D x ω‖ ≤ C)
    (hD : ∀ᵐ ω ∂P,∀ x,HasFDerivAt (fun z => f z ω) (D x ω) x) :
    ∀ x,HasFDerivAt (fun z => ∫ ω,f z ω ∂P) (∫ ω,D x ω ∂P) x := by
  intro x
  have hi : Integrable (f x) P := Integrable.mono' (integrable_const B) (hf x) (hfb x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C)
    (by simp) (Eventually.of_forall hf) hi (hDm x)
    (hDb.mono (fun ω h z _ => h z)) (integrable_const C)
    (hD.mono (fun ω h z _ => h z))

end Asakura.Chapter8
