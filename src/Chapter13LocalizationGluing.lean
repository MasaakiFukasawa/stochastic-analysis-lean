import Chapter13LocalParameterFubini

open MeasureTheory Set
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The HJM localizers eventually become infinite pathwise. Countably many
stopped process identities therefore yield one common-event unstopped identity. -/
theorem eventually_top_stopped_identity {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (τ:ℕ → Ω → HalfClosedTime)
    (htop:∀w,∃N:ℕ,∀n,N≤n → τ n w=⊤)
    (X Y:HalfClosedTime → Ω → ℝ)
    (he:∀n,∀ᵐw∂P,∀t,X (min (τ n w) t) w=Y (min (τ n w) t) w) :
    ∀ᵐw∂P,∀t,X t w=Y t w := by
  filter_upwards [ae_all_iff.mpr he] with w hw
  obtain ⟨n,hn⟩:=htop w
  intro t
  simpa [hn n le_rfl] using hw n t

/-- The same argument on a finite interval suffices for HJM, since the
Brownian integrals have also been stopped at the deterministic endpoint. -/
theorem eventually_top_finite_stopped_identity {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (τ:ℕ → Ω → HalfClosedTime)
    (htop:∀w,∃N:ℕ,∀n,N≤n → τ n w=⊤)
    (R:HalfClosedTime) (X Y:HalfClosedTime → Ω → ℝ)
    (he:∀n,∀ᵐw∂P,∀t,X (min (min (τ n w) R) t) w=Y (min (min (τ n w) R) t) w) :
    ∀ᵐw∂P,∀t,t≤R → X t w=Y t w := by
  filter_upwards [ae_all_iff.mpr he] with w hw
  obtain ⟨n,hn⟩:=htop w
  intro t ht
  simpa [hn n le_rfl,min_eq_right ht] using hw n t
end Asakura.Chapter13
#print axioms Asakura.Chapter13.eventually_top_stopped_identity
#print axioms Asakura.Chapter13.eventually_top_finite_stopped_identity
