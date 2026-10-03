import Chapter2SquareIntegrableStop

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000

/-- The final local-martingale step in the completeness proof. A pathwise
limit with continuous paths and common bounded localizers is again local.
This explicitly verifies all conditional-expectation equations after stopping.
The construction of those common localizers from a Cauchy subsequence is a
separate obligation, not an assumption hidden in a completeness instance. -/
theorem local_limit_of_common_bounded_stops
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ℕ → ClosedTime T → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P F (X n))
    (Y : ClosedTime T → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => Y s ω) t)
    (hconv : ∀ ω t, t < ⊤ → Tendsto (fun n => X n t ω) atTop (𝓝 (Y t ω)))
    (σ : ℕ → Ω → ClosedTime T)
    (hσ : ∀ k t, MeasurableSet[F t] {ω | σ k ω ≤ t})
    (hσmono : ∀ ω, Monotone (fun k => σ k ω))
    (hσtop : ∀ k ω, σ k ω < ⊤)
    (hσcofinal : ∀ ω t, t < ⊤ → ∃ k, t < σ k ω)
    (K : ℕ → ℝ)
    (hbound : ∀ k n, ∀ᵐ ω ∂P, ∀ t, ‖X n (min (σ k ω) t) ω‖ ≤ K k) :
    LocalMProcessWitness P F Y := by
  refine ⟨σ,hσ,hσmono,hσtop,hσcofinal,?_⟩
  intro k
  let Z := fun n t ω => X n (min (σ k ω) t) ω
  have hZ (n) : Z n ∈ boundedMProcess P F :=
    bounded_local_stop_is_bounded_martingale P F hF hle (X n) (hX n)
      (σ k) (hσ k) (hσtop k) (K k) (hbound k n)
  have hcv (ω t) : Tendsto (fun n => Z n t ω) atTop (𝓝 (Y (min (σ k ω) t) ω)) :=
    hconv ω _ ((min_le_left _ _).trans_lt (hσtop k ω))
  have hm (t) : Measurable[F t] (fun ω => Y (min (σ k ω) t) ω) := by
    letI : MeasurableSpace Ω := F t
    apply measurable_of_tendsto_metrizable (fun n => (hZ n).1.adapted t)
    rw [tendsto_pi_nhds]
    exact fun ω => hcv ω t
  have hcont (ω) : Continuous (fun t => Y (min (σ k ω) t) ω) := by
    apply continuous_iff_continuousAt.2
    intro t
    exact (hc ω _ ((min_le_left _ _).trans_lt (hσtop k ω))).comp
      (continuous_const.min continuous_id).continuousAt
  have hb (t) : ∀ᵐ ω ∂P, ‖Y (min (σ k ω) t) ω‖ ≤ K k := by
    filter_upwards [ae_all_iff.2 (hbound k)] with ω hω
    exact le_of_tendsto (hcv ω t).norm (Filter.Eventually.of_forall fun n => hω n t)
  have hM := dominated_continuous_martingale_limit P F hle Z (fun n => (hZ n).1)
    _ hm hcont (fun _ => K k) (memLp_const (K k))
    (fun n t => (hbound k n).mono fun ω hω => hω t)
    (fun t => Filter.Eventually.of_forall fun ω => hcv ω t)
  exact ⟨hM,fun t => memLp_top_of_bound ((hm t).mono (hle t) le_rfl).aestronglyMeasurable (K k) (hb t)⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_limit_of_common_bounded_stops
