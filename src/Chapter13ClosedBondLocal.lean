import Chapter13MartingaleClosure
import Chapter2LevelLocalization

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The closed discounted bond martingale supplied by H8 is a local
martingale once its continuous realization is identified. No L2 hypothesis
is inserted at this step. -/
theorem closed_bond_centered_local {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (Z:Ω → ℝ) (hi:Integrable Z P) (Y:ClosedTime T → Ω → ℝ)
    (hm:∀t,Measurable[F t] (Y t)) (hc:∀w,Continuous (fun t => Y t w))
    (he:∀t,Y t=ᵐ[P] P[Z|F t]) :
    LocalMProcessWitness P F (fun t w => Y t w-Y ⊥ w) := by
  have hYi t:Integrable (Y t) P := (integrable_condExp (μ:=P) (m:=F t) (f:=Z)).congr (he t).symm
  have hYm s t (hst:s≤t):P[Y t|F s]=ᵐ[P] Y s :=
    (condExp_congr_ae (he t)).trans ((condExp_condExp_of_le (hF hst) (hle t)).trans (he s).symm)
  have hmart s t (hst:s≤t):P[(fun w => Y t w-Y ⊥ w)|F s]=ᵐ[P] (fun w => Y s w-Y ⊥ w) := by
    have hsub:=condExp_sub (hYi t) (hYi ⊥) (F s)
    have hz:=condExp_of_stronglyMeasurable (hle s) ((hm ⊥).mono (hF bot_le) le_rfl).stronglyMeasurable (hYi ⊥)
    filter_upwards [hsub,hYm s t hst] with w hw ht
    change P[(fun w => Y t w-Y ⊥ w)|F s] w=P[Y t|F s] w-P[Y ⊥|F s] w at hw
    rw [hw,ht,hz]
  apply continuous_lp_martingale_is_local P hT F hF hle 1 le_rfl
    (fun t w => Y t w-Y ⊥ w)
  · intro t
    exact (hm t).sub ((hm ⊥).mono (hF bot_le) le_rfl)
  · intro t
    exact memLp_one_iff_integrable.mpr ((hYi t).sub (hYi ⊥))
  · intro w
    exact (hc w).sub continuous_const
  · exact hmart
  · exact ae_of_all _ fun w => sub_self _
end Asakura.Chapter13
#print axioms Asakura.Chapter13.closed_bond_centered_local
