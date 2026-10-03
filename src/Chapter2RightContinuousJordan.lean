import Chapter2RightContinuousVariation
import Chapter2ActualLocalVariation
import FullAuditVariationStopping

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Right-continuous adapted BV paths have adapted right-continuous
Jordan parts. This includes jumps, exactly as in the manuscript's A. -/
theorem adapted_right_continuous_jordan_decomposition
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (X : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (X t))
    (hr : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hb : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) : AdaptedVariationWitness F X := by
  let A := fun t ω => pathVariation (fun s => X s ω) t
  have hAm t : Measurable[F t] (A t) := right_continuous_variation_adapted F hF X hm hr t
  have he ω t : variationOnFromTo (fun s => X s ω) univ ⊥ t = A t ω := by
    rw [variationOnFromTo.eq_of_le _ _ bot_le,univ_inter,Icc_bot]
    rfl
  have hAr ω t : ContinuousWithinAt (fun s => A s ω) (Ici t) t := by
    have h := (hb ω).continuousWithinAt_variationOnFromTo_Ici (a := (⊥ : ClosedTime T)) (hr ω t)
    have hef : variationOnFromTo (fun s => X s ω) univ ⊥ = (fun s => A s ω) := funext (he ω)
    rw [hef] at h
    exact h
  refine ⟨fun t ω => (A t ω+X t ω)/2,fun t ω => (A t ω-X t ω)/2,?_,?_,?_,?_⟩
  · intro t
    exact ⟨((hAm t).add (hm t)).div_const 2,((hAm t).sub (hm t)).div_const 2⟩
  · intro ω
    constructor
    · intro s t hst
      have h := variationOnFromTo.add_self_monotoneOn (hb ω).locallyBoundedVariationOn
        (mem_univ (⊥ : ClosedTime T)) (mem_univ s) (mem_univ t) hst
      simp only [Pi.add_apply,he] at h
      exact div_le_div_of_nonneg_right h (by norm_num)
    · intro s t hst
      have h := variationOnFromTo.sub_self_monotoneOn (hb ω).locallyBoundedVariationOn
        (mem_univ (⊥ : ClosedTime T)) (mem_univ s) (mem_univ t) hst
      simp only [Pi.sub_apply,he] at h
      exact div_le_div_of_nonneg_right h (by norm_num)
  · intro ω t
    exact ⟨((hAr ω t).add (hr ω t)).div_const 2,((hAr ω t).sub (hr ω t)).div_const 2⟩
  · intro t ω; dsimp only; ring

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.adapted_right_continuous_jordan_decomposition
