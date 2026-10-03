import Chapter3DiscreteQVFinite

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The finite orthogonality identity at an arbitrary deterministic time.
Stopping X and Q at that time proves the statement without requiring the
partition intervals to have ended before that time. -/
theorem discrete_qv_finite_energy_at_time
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτmono : ∀ ω, Monotone (fun j => τ j ω)) (hτtop : ∀ j ω, τ j ω < ⊤)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω‖ ≤ δ)
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P) (N : ℕ) (t : ClosedTime T) :
    (∫ ω, (∑ j ∈ Finset.range N, A j ω*partitionDefect X Q τ j t ω)^2 ∂P) =
      ∑ j ∈ Finset.range N, ∫ ω, (A j ω*partitionDefect X Q τ j t ω)^2 ∂P := by
  have hs : ∀ r, MeasurableSet[F r] {ω : Ω | t ≤ r} := by
    intro r
    by_cases h : t ≤ r <;> simp [h]
  let Xt := fun r ω => X (min t r) ω
  let Qt := fun r ω => Q (min t r) ω
  have hbt (j) : ∀ᵐ ω ∂P, ∀ r,
      ‖Xt (min (τ (j+1) ω) r) ω-Xt (min (τ j ω) r) ω‖ ≤ δ := by
    filter_upwards [hb j] with ω hω
    intro r
    simpa only [Xt,min_left_comm t] using hω (min t r)
  have hh := discrete_qv_finite_energy P F hF hle hnull Xt Qt
    (hX.stopped P F hF hle (fun _ => t) hs) (hQ.stopped P F hF hle (fun _ => t) hs)
    τ hτ hτmono hτtop δ hδ hbt A hA hAb N
  simpa only [partitionDefect,Xt,Qt,min_top_right,min_comm t] using hh

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.discrete_qv_finite_energy_at_time
