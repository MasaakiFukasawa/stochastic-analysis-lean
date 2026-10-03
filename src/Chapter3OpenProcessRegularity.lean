import Chapter3RegularizedWeightRegularity
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Open-interval adaptation and continuity suffice at a finite stopping time;
no arbitrary terminal value is required to be measurable. -/
theorem open_process_stopped_regular
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (Y : ClosedTime T → Ω → ℝ)
    (ha : ∀ t, t < ⊤ → Measurable[F t] (Y t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y s ω) t)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) :
    (∀ t, Measurable[F t] (fun ω => Y (min (σ ω) t) ω)) ∧
    (∀ ω, Continuous (fun t => Y (min (σ ω) t) ω)) := by
  classical
  let Z := fun t ω => if t < ⊤ then Y t ω else 0
  have hZa t : Measurable[F t] (Z t) := by
    by_cases ht : t < ⊤
    · simpa only [Z,if_pos ht] using ha t ht
    · simpa only [Z,if_neg ht] using (measurable_const : Measurable[F t] (fun _ : Ω => (0:ℝ)))
  have hZc ω t (ht : t < ⊤) : ContinuousAt (fun s => Z s ω) t :=
    (hc ω t ht).congr_of_eventuallyEq ((gt_mem_nhds ht).mono (fun s hs => if_pos hs))
  have hZr ω t : ContinuousWithinAt (fun s => Z s ω) (Ici t) t := by
    by_cases ht : t < ⊤
    · exact (hZc ω t ht).continuousWithinAt
    · have he : t = ⊤ := top_le_iff.mp (le_of_not_gt ht)
      subst t
      simp only [Ici_top]
      exact continuousWithinAt_singleton
  have he : (fun t ω => Z (min (σ ω) t) ω) = (fun t ω => Y (min (σ ω) t) ω) := by
    funext t ω
    exact if_pos ((min_le_left _ _).trans_lt (hσt ω))
  constructor
  · intro t
    have hh := stopped_min_value_measurable F hF σ hσ Z hZa hZr t
    have ht := congrFun he t
    rw [ht] at hh
    exact hh
  · intro ω
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hc ω _ ((min_le_left _ _).trans_lt (hσt ω))).comp
      (continuous_const.min continuous_id).continuousAt

theorem LocalMProcessWitness.congr_ae_open
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    {X Y : ClosedTime T → Ω → ℝ} (hX : LocalMProcessWitness P F X)
    (ha : ∀ t, t < ⊤ → Measurable[F t] (Y t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y s ω) t)
    (he : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = Y t ω) : LocalMProcessWitness P F Y :=
  hX.congr_ae_of_stopped_regular P F he (fun σ hσ hσt => open_process_stopped_regular F hF Y ha hc σ hσ hσt)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.open_process_stopped_regular
#print axioms Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open
