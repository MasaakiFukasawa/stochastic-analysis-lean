import Chapter3CommonOscillationPartition
import Chapter2ActualLocalVariation
import Chapter2ItoConstructionChoices

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- A continuous adapted increasing process belongs to A_loc, with no
assumption at the excluded terminal time. -/
theorem continuous_increasing_adapted_variation
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (A : ClosedTime T → Ω → ℝ)
    (ha : ∀ t, t < ⊤ → Measurable[F t] (A t))
    (hm : ∀ ω, MonotoneOn (fun t => A t ω) (Iio ⊤))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => A s ω) t) :
    AdaptedLocalVariationWitness F A := by
  obtain ⟨c,_,_,_,hcm,hct,hco⟩ := positive_real_time_exhaustion hT
  refine ⟨fun n _ => realTimeClamp (c n),?_,fun _ => hcm.monotone,
    fun n _ => hct n,fun _ => hco,?_⟩
  · intro n t
    by_cases h : realTimeClamp (T := T) (c n) ≤ t <;> simp [h]
  · intro n
    refine ⟨(fun t ω => A (min (realTimeClamp (c n)) t) ω),(fun _ _ => 0),?_,?_,?_,?_⟩
    · intro t
      exact ⟨(ha _ ((min_le_left _ _).trans_lt (hct n))).mono (hF (min_le_right _ _)) le_rfl,
        measurable_const⟩
    · intro ω
      refine ⟨?_,monotone_const⟩
      intro s t hst
      exact hm ω ((min_le_left _ _).trans_lt (hct n)) ((min_le_left _ _).trans_lt (hct n))
        (min_le_min_left _ hst)
    · intro ω t
      exact ⟨((hc ω _ ((min_le_left _ _).trans_lt (hct n))).comp
        (continuous_const.min continuous_id).continuousAt).continuousWithinAt,continuousWithinAt_const⟩
    · intro t ω
      simp only [sub_zero]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_increasing_adapted_variation
