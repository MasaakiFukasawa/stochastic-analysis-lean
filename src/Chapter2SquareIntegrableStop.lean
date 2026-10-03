import Chapter2DominatedMartingaleLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- Proposition prop244, the martingale conclusion in (ii) => (iii):
a local martingale stopped strictly before T, with a square-integrable
pathwise bound, is a continuous M2 martingale on the closed interval. -/
theorem local_stop_is_m2_of_square_integrable_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)
    (B : Ω → ℝ) (hB : MemLp B 2 P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ ω) t) ω‖ ≤ B ω) :
    ContinuousM2Witness P F (fun t ω => X (min (σ ω) t) ω) := by
  obtain ⟨τ,ht,htm,htt,htc,hXτ⟩ := hX.localizers
  let Z := fun n t ω => X (min (τ n ω) (min (σ ω) t)) ω
  have hZ (n) : ContinuousM2Witness P F (Z n) :=
    continuous_m2_stopped P F hF hle (fun t ω => X (min (τ n ω) t) ω)
      (hXτ n).1 σ hσ
  have he (ω t) : ∀ᶠ n in atTop, Z n t ω = X (min (σ ω) t) ω := by
    obtain ⟨n,hn⟩ := htc ω (σ ω) (hσtop ω)
    refine eventually_atTop.2 ⟨n, fun k hk => ?_⟩
    dsimp [Z]
    rw [← min_assoc, min_eq_right (hn.le.trans (htm ω hk))]
  have hYm (t) : Measurable[F t] (fun ω => X (min (σ ω) t) ω) :=
    @glued_value_measurable Ω (F t) (fun n ω => Z n t ω)
      (fun n => (hZ n).adapted t) _ (fun ω => he ω t)
  have hYc (ω) : Continuous (fun t => X (min (σ ω) t) ω) := by
    apply continuous_iff_continuousAt.2
    intro t
    exact (hX.path P F ω _ ((min_le_left _ _).trans_lt (hσtop ω))).comp
      (continuous_const.min continuous_id).continuousAt
  apply dominated_continuous_martingale_limit P F hle Z hZ _ hYm hYc B hB
  · intro n t
    filter_upwards [hbound] with ω hω
    simpa only [Z, min_left_comm] using hω (min (τ n ω) t)
  · intro t
    exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.congr'
      (show (fun _ : ℕ => X (min (σ ω) t) ω) =ᶠ[atTop] (fun n => Z n t ω) from
        (he ω t).mono fun n hn => hn.symm)

/-- The last assertion of prop244: a uniformly bounded stopped local
martingale is a bounded continuous martingale. -/
theorem bounded_local_stop_is_bounded_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)
    (K : ℝ) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ ω) t) ω‖ ≤ K) :
    (fun t ω => X (min (σ ω) t) ω) ∈ boundedMProcess P F := by
  have hM := local_stop_is_m2_of_square_integrable_bound P F hF hle X hX σ hσ hσtop
    (fun _ => K) (memLp_const K) hbound
  refine ⟨hM, ?_⟩
  intro t
  exact memLp_top_of_bound ((hM.adapted t).mono (hle t) le_rfl).aestronglyMeasurable K
    (hbound.mono fun ω hω => hω t)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_stop_is_m2_of_square_integrable_bound

#print axioms Asakura.Chapter2Complete.bounded_local_stop_is_bounded_martingale
