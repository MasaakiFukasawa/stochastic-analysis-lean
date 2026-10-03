import Chapter10ForcedPathStability

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Equal initial values and identical past forcing determine the same past
solution. This is the step used to prove adaptation of the constructed flow. -/
theorem time_dependent_solution_causal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (b : ℝ → E → E) (K : ℝ≥0) (hbc : Continuous (Function.uncurry b))
    (hb : ∀ t,LipschitzWith K (b t))
    (X Y W V : ℝ → E) (hcX : Continuous X) (hcY : Continuous Y)
    (x : E) (T : ℝ) (hT : 0≤T)
    (hWV : ∀ t∈Icc 0 T,W t=V t)
    (hX : ∀ t∈Icc 0 T,X t=x+(∫ s in 0..t,b s (X s))+W t)
    (hY : ∀ t∈Icc 0 T,Y t=x+(∫ s in 0..t,b s (Y s))+V t) :
    ∀ t∈Icc 0 T,X t=Y t := by
  have hh := time_dependent_forced_path_stability b K hbc hb X Y W V hcX hcY x x T 0 hT le_rfl
    (fun t ht => by rw [hWV t ht,sub_self,norm_zero]) hX hY
  intro t ht
  have hn := hh t ht
  simp only [sub_self,norm_zero,zero_add,mul_zero] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

end Asakura.Chapter10
