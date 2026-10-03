import Chapter2DominatedMartingaleLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000

/-- A local martingale continuous at the finite terminal time is a closed
M² martingale whenever its entire path has an L² bound. This includes the
terminal value, which an open-interval local witness by itself does not control. -/
theorem closed_local_martingale_of_path_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hle : ∀ t,F t ≤ m) (X : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (ha : ∀ t,Measurable[F t] (X t)) (hc : ∀ w,Continuous (fun t => X t w))
    (B : Ω → ℝ) (hB : MemLp B 2 P) (hb : ∀ᵐ w ∂P,∀ t,‖X t w‖ ≤ B w) :
    ContinuousM2Witness P F X := by
  obtain ⟨τ,ht,hm,htt,hco,hM⟩ := hX.localizers
  have hlim w : Tendsto (fun n => τ n w) atTop (𝓝 ⊤) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      obtain ⟨n,hn⟩ := hco w a ha
      exact eventually_atTop.mpr ⟨n,fun k hk => hn.trans_le (hm w hk)⟩
    · intro a ha
      exact (not_lt_of_ge le_top ha).elim
  apply dominated_continuous_martingale_limit P F hle
    (fun n t w => X (min (τ n w) t) w) (fun n => (hM n).1) X ha hc B hB
  · intro n t
    exact hb.mono fun w hw => hw _
  · intro t
    apply ae_of_all
    intro w
    have hh := (hlim w).min (tendsto_const_nhds (x := t))
    rw [min_top_left] at hh
    exact (hc w).continuousAt.tendsto.comp hh

end Asakura.Chapter7
