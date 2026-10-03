import Chapter8AdditiveFlowC1

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The first variational derivative has a deterministic bound, uniform
in the forcing path and initial state. -/
theorem additive_flow_derivative_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (X : E → ℝ → E) (J : ℝ → E →L[ℝ] E)
    (x : E) (T A : ℝ) (hA : 0 ≤ A)
    (hLip : ∀ x y t,t∈Icc 0 T → ‖X x t-X y t‖ ≤ A*‖x-y‖)
    (hJ : ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J t) x) :
    ∀ t,t∈Icc 0 T → ‖J t‖ ≤ A := by
  intro t ht
  apply (hJ t ht).le_of_lipschitz (C := ⟨A,hA⟩)
  apply LipschitzWith.of_dist_le_mul
  intro z y
  change dist (X z t) (X y t) ≤ A*dist z y
  simpa only [dist_eq_norm] using hLip z y t ht

end Asakura.Chapter8
