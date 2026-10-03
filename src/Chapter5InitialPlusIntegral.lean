import Chapter5ClockSemimartingale

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- An initially measurable variable plus an actual local Ito integral
is a semimartingale on the ambient time domain. -/
theorem initial_plus_local_integral_semimartingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (U : Ω → ℝ) (hU : Measurable[F ⊥] U)
    (M : ClosedTime T → Ω → ℝ) (hM : LocalMProcessWitness P F M) :
    SemimartingaleDecomposition P F (fun t w => U w+M t w) (fun _ => U) M := by
  have hconst : AdaptedVariationWitness F (fun _ => U) := by
    refine ⟨(fun _ => U),(fun _ _ => 0),?_,?_,?_,?_⟩
    · exact fun t => ⟨hU.mono (hF bot_le) le_rfl,measurable_const⟩
    · exact fun _ => ⟨monotone_const,monotone_const⟩
    · exact fun _ _ => ⟨continuousWithinAt_const,continuousWithinAt_const⟩
    · exact fun _ _ => (sub_zero _).symm
  exact ⟨global_variation_localized hT F hF _ hconst,hM,
    (fun w t ht => continuousAt_const.add (hM.path P F w t ht)),fun _ _ _ => rfl⟩

end Asakura.Chapter5
