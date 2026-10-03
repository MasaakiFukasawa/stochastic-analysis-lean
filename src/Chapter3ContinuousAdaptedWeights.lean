import Chapter3LocalizedQuadraticApproximation
import Chapter3OscillationPartitionFormula

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- Adapted continuous weights have measurable stopping values and bounded
stopping values whenever their paths are bounded by K. These are derived
properties of H, not extra hypotheses on the partition coefficients. -/
theorem continuous_adapted_stopping_weights
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (H : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, Measurable[F t] (H t)) (hc : ∀ ω, Continuous (fun t => H t ω))
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (K : ℝ) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ K) :
    Measurable[writtenStoppedSpace m F σ hσ] (fun ω => H (σ ω) ω) ∧
    MemLp (fun ω => H (σ ω) ω) ∞ P ∧
    (∀ᵐ ω ∂P, |H (σ ω) ω| ≤ K) := by
  have h := stopped_value_measurable_right_continuous m (show (0:EReal) ≤ T from Fact.out)
    F hF hle σ hσ H hm (fun ω t => (hc ω).continuousAt.continuousWithinAt)
  have hB : ∀ᵐ ω ∂P, |H (σ ω) ω| ≤ K := hb.mono (fun ω hω => hω (σ ω))
  refine ⟨h,?_,hB⟩
  apply memLp_top_of_bound (h.mono (fun A hA => hA.1) le_rfl).aestronglyMeasurable K
  simpa only [Real.norm_eq_abs] using hB

/-- A continuous adapted process on the open time interval remains adapted
and continuous after a strictly finite stopping time. This generalizes the
previous martingale-specific bridge and will be used to localize H. -/
theorem open_continuous_adapted_stopped_regular
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (H : ClosedTime T → Ω → ℝ)
    (hm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) :
    (∀ t, Measurable[F t] (fun ω => H (min (σ ω) t) ω)) ∧
    (∀ ω, Continuous (fun t => H (min (σ ω) t) ω)) := by
  let Z := fun n t ω => H (min (c n) t) ω
  have hZm (n t) : Measurable[F t] (Z n t) :=
    (hm _ ((min_le_left _ _).trans_lt (hct n))).mono (hF (min_le_right _ _)) le_rfl
  have hZc (n ω) : Continuous (fun t => Z n t ω) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc ω _ ((min_le_left _ _).trans_lt (hct n))).comp
      (continuous_const.min continuous_id).continuousAt
  constructor
  · intro t
    have hsm (n) := stopped_min_value_measurable F hF σ hσ (Z n) (hZm n)
      (fun ω t => (hZc n ω).continuousAt.continuousWithinAt) t
    apply @glued_value_measurable Ω (F t) (fun n ω => Z n (min (σ ω) t) ω) hsm
    intro ω
    obtain ⟨N,hN⟩ := hcc (σ ω) (hσt ω)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact congrArg (fun s => H s ω) (min_eq_right ((min_le_left _ _).trans (hN.le.trans (hcm hn))))
  · intro ω
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc ω _ ((min_le_left _ _).trans_lt (hσt ω))).comp
      (continuous_const.min continuous_id).continuousAt

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.continuous_adapted_stopping_weights
#print axioms Asakura.Chapter3Complete.open_continuous_adapted_stopped_regular
