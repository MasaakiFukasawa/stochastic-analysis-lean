import FullAuditProgressive
import Chapter2ProgressiveSpace

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Multiplying a continuous adapted error by a deterministic Borel feedback
coefficient preserves progressiveness, even if the coefficient diverges near
maturity. Its assigned value at maturity need not be a continuity value. -/
theorem kyle_feedback_progressive {Ω : Type*} {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (p : ClosedTime T → Ω → ℝ) (V : Ω → ℝ)
    (hp : ∀ t,Measurable[F t] (p t)) (hV : Measurable[F ⊥] V)
    (hc : ∀ w,Continuous (fun t => p t w))
    (β : ClosedTime T → ℝ) (hβ : Measurable β) :
    @Measurable _ _ (progressiveSpace F) inferInstance
      (fun z : Ω × ClosedTime T => β z.2*(V z.1-p z.2 z.1)) := by
  apply (measurable_progressive_iff _ _).mpr
  intro t
  letI : MeasurableSpace Ω := F t
  have he := right_continuous_progressive_written F hF (fun s w => V w-p s w)
    (fun s => (hV.mono (hF bot_le) le_rfl).sub (hp s))
    (fun w s => (continuous_const.sub (hc w)).continuousWithinAt) t
  have he' : Measurable (fun z : Ω × Iic t => V z.1-p z.2.val z.1) :=
    he.comp measurable_swap
  exact (hβ.comp (measurable_subtype_coe.comp measurable_snd)).mul he'

end Asakura.Chapter10
