import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The deterministic clock hypothesis already supplies the auxiliary
monotonicity and continuity used by the stochastic moment estimates. -/
theorem clock_regular_from_identity
    {Ω : Type*} {T : EReal} [Fact (0≤T)] (C : ClosedTime T → Ω → ℝ)
    (hclock : ∀ w (r : ℝ),0≤r → (r:EReal)<T → C (realTimeClamp r) w=r) :
    (∀ w,MonotoneOn (fun t => C t w) (Iio ⊤)) ∧
    (∀ w t,t<⊤ → ContinuousAt (fun s => C s w) t) := by
  have he w t (ht : t<⊤) : C t w=(t:EReal).toReal := by
    obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t ht
    rw [hclock w r hr hrT,real_time_clamp_eq r hr hrT.le,EReal.toReal_coe]
  constructor
  · intro w s hs t ht hst
    dsimp only
    rw [he w s hs,he w t ht]
    exact EReal.toReal_le_toReal hst
      (ne_of_gt ((EReal.bot_lt_coe 0).trans_le s.property.1))
      (ne_of_lt ((show (t:EReal)<T from ht).trans_le le_top))
  · intro w t ht
    have hreal : ContinuousAt (fun s : ClosedTime T => (s:EReal).toReal) t :=
      (EReal.tendsto_toReal (ne_of_lt ((show (t:EReal)<T from ht).trans_le le_top))
        (ne_of_gt ((EReal.bot_lt_coe 0).trans_le t.property.1))).comp continuous_subtype_val.continuousAt
    apply hreal.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds ht] with s hs
    exact he w s hs

end Asakura.Chapter4
