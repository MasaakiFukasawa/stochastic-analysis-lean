import Chapter2LowerBoundedLocal

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A zero-initial actual local martingale with a deterministic lower bound
on the investment horizon cannot give a positive terminal gain. Localization
and terminal integrability are derived, not assumed. -/
theorem no_arbitrage_actual_local_wealth {Ω : Type*} [m : MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure Q] (hPQ : P≪Q)
    {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness Q F X)
    (R : ClosedTime T) (hR : R<⊤) (a : ℝ)
    (hb : ∀ᵐ w ∂Q,∀ t,t≤R → -a≤X t w)
    (hn : 0≤ᵐ[Q] X R) : X R=ᵐ[P] 0 := by
  obtain ⟨τ,ht,hm,htt,hc,hXτ⟩ := hX.localizers
  let Y := fun n w => X (min (τ n w) R) w
  have hYi n : Integrable (Y n) Q := ((hXτ n).1.moment R).integrable (by norm_num)
  have hmean n : (∫ w,Y n w ∂Q)=0 := by
    have he := ((hXτ n).1.martingale ⊥ R bot_le).trans (hXτ n).1.initial
    have hi := integral_congr_ae he
    rw [integral_condExp (hle ⊥)] at hi
    simpa only [Pi.zero_apply,integral_zero] using hi
  have hlim : ∀ᵐ w ∂Q,Tendsto (fun n => Y n w) atTop (𝓝 (X R w)) := by
    apply Eventually.of_forall
    intro w
    obtain ⟨n,hn⟩ := hc w R hR
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    dsimp only [Y]
    rw [min_eq_right (hn.le.trans (hm w hk))]
  exact no_arbitrage_from_localized_wealth P Q hPQ Y (X R) hYi hmean a
    (fun n => hb.mono (fun w hw => hw _ (min_le_right _ _))) hlim hn

/-- Positive bank-account discounting preserves the terminal zero-payoff
conclusion, even for a random short rate. -/
theorem undiscount_zero_payoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V B : Ω → ℝ) (hB : ∀ᵐ w ∂P,B w≠0)
    (hzero : (fun w => V w/B w)=ᵐ[P] 0) : V=ᵐ[P] 0 := by
  filter_upwards [hB,hzero] with w hw hz
  exact (div_eq_zero_iff.mp hz).resolve_right hw

end Asakura.Chapter11
