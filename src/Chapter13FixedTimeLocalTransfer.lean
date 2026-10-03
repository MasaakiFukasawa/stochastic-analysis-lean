import Chapter5BracketCommonTime
import Chapter3OpenProcessRegularity

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Fixed-time identities identify continuous local martingale processes
on one common event, even though the open terminal value is unspecified. -/
theorem local_transfer_fixed_time {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F)
    (X Y:ClosedTime T → Ω → ℝ) (hX:LocalMProcessWitness P F X)
    (ha:∀t,t<⊤ → Measurable[F t] (Y t))
    (hc:∀w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (he:∀t,t<⊤ → X t=ᵐ[P] Y t) : LocalMProcessWitness P F Y := by
  letI:Nonempty (Iio (⊤:ClosedTime T)):=⟨⟨⊥,hT⟩⟩
  have hx:∀w,Continuous (fun t:Iio (⊤:ClosedTime T) => X t.val w) := by
    intro w
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hX.path P F w t.val t.property).comp continuous_subtype_val.continuousAt
  have hy:∀w,Continuous (fun t:Iio (⊤:ClosedTime T) => Y t.val w) := by
    intro w
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc w t.val t.property).comp continuous_subtype_val.continuousAt
  have hh:=ae_continuous_common_time_equality P (fun t:Iio (⊤:ClosedTime T) => X t.val)
    (fun t:Iio (⊤:ClosedTime T) => Y t.val) (ae_of_all _ hx) (ae_of_all _ hy) (fun t => he t.val t.property)
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open P F hF hX ha hc
  exact hh.mono (fun w hw t ht => hw ⟨t,ht⟩)
end Asakura.Chapter13
#print axioms Asakura.Chapter13.local_transfer_fixed_time
