import Chapter8ForcedInitialStability

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- Identify the constructed path with any solution of the same additive
integral equation, on the entire finite time interval. -/
theorem additive_path_unique {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (K : ℝ≥0) (hb : LipschitzWith K b)
    (X Y W : ℝ → E) (hcX : Continuous X) (hcY : Continuous Y)
    (x : E) (T : ℝ) (hT : 0 ≤ T)
    (hX : ∀ t,t∈Icc 0 T → X t=x+(∫ s in 0..t,b (X s))+W t)
    (hY : ∀ t,t∈Icc 0 T → Y t=x+(∫ s in 0..t,b (Y s))+W t) :
    ∀ t,t∈Icc 0 T → X t=Y t := by
  intro t ht
  have hh := forced_initial_stability b K hb X Y W hcX hcY x x T hT hX hY t ht
  have hn : ‖X t-Y t‖ ≤ 0 := by simpa only [sub_self,norm_zero,mul_zero] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

end Asakura.Chapter8
