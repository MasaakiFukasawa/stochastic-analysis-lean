import Chapter2LocalProcess
import FullAuditNoArbitrage

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- The first Fatou step in prop:fatou, including integrability of every
stopped value. The stopped expectations and pointwise limits are derived
from actual localizers, rather than supplied as abstract hypotheses. -/
theorem lower_bounded_local_stopped_integrable
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (a : ℝ)
    (hbound : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → -a ≤ X t ω) :
    Integrable (fun ω => X (σ ω) ω) P ∧ (∫ ω, X (σ ω) ω ∂P) ≤ 0 := by
  obtain ⟨τ,ht,hm,htt,hc,hXτ⟩ := hX.localizers
  let Z := fun n t ω => X (min (τ n ω) (min (σ ω) t)) ω
  have hZ (n) : ContinuousM2Witness P F (Z n) :=
    continuous_m2_stopped P F hF hle (fun t ω => X (min (τ n ω) t) ω)
      (hXτ n).1 σ hσ
  have hmean (n) : (∫ ω, Z n ⊤ ω ∂P) = 0 := by
    have h := integral_congr_ae (((hZ n).martingale ⊥ ⊤ le_top).trans (hZ n).initial)
    rw [integral_condExp (hle ⊥)] at h
    simpa only [Pi.zero_apply,integral_zero] using h
  apply localized_wealth_fatou P (fun n => Z n ⊤) (fun ω => X (σ ω) ω)
    (fun n => ((hZ n).moment ⊤).integrable (by norm_num)) hmean a
  · intro n
    exact hbound.mono fun ω hω => hω _ ((min_le_left _ _).trans_lt (htt n ω))
  · apply Filter.Eventually.of_forall
    intro ω
    obtain ⟨n,hn⟩ := hc ω (σ ω) (hσtop ω)
    apply tendsto_const_nhds.congr'
    refine eventually_atTop.2 ⟨n,fun k hk => ?_⟩
    simp only [Z,min_top_right,min_eq_right (hn.le.trans (hm ω hk))]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.lower_bounded_local_stopped_integrable
