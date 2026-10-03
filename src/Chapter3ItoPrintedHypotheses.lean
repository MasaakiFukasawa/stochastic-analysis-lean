import Chapter3GeneralItoApproximation
import Chapter3PartitionEssentialBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Karandikar approximation from the manuscript's original hypotheses.
The regular quadratic variation, time exhaustion, common-null-set bounds,
localization and actual discrete-integral identification are all supplied
by the proved constructions. -/
theorem ito_approximation_from_essential_bounds
    {Ω ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X H Y : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (hY : LocalMProcessWitness P F Y)
    (hYI : ItoCovarianceFormula P F X (fun z => H (realTimeClamp z.2) z.1) Y)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτm : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτt : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hτc : ∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω)
    (q : ι → Iio (⊤ : ClosedTime T)) (hq : DenseRange q)
    (hbH : ∀ n j i, eLpNorm (fun ω =>
      H (min (τ n (j+1) ω) (q i).val) ω-H (min (τ n j ω) (q i).val) ω) ∞ P ≤ ENNReal.ofReal ((1/2:ℝ)^n))
    (b : ClosedTime T) (hb : b < ⊤) :
    ∀ᵐ ω ∂P, TendstoUniformly
      (fun n t => ∑' j, H (τ n j ω) ω*
        (X (min (τ n (j+1) ω) (min b t)) ω-X (min (τ n j ω) (min b t)) ω))
      (fun t => Y (min b t) ω) atTop := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion hT
  obtain ⟨A,hA,hAm,hAc,hA0⟩ := local_quadratic_variation_regular_choice P F hF hle hnull X hX
  have hreg j := regular_covariance_on_real_intervals A hAm hAc (c j) (hc j).le (hcT j)
  have hh n j := stopped_dense_essential_bound P q hq H hHc
    (τ n j) (τ n (j+1)) (fun ω => hτm n ω (Nat.le_succ j)) (hτt n (j+1))
    ((1/2:ℝ)^n) (pow_nonneg (by norm_num) n) (hbH n j)
  exact general_ito_approximation P hT F hF hle hnull X A H Y hX hA hY hYI hHm hHc
    c hc hcm hcT hct hcut hcc (fun j => (hreg j).1) (fun j => (hreg j).2) hA0
    τ hτ hτm hτt hτ0 hτc (stopped_bound_interval_oscillation P H τ (fun n => (1/2:ℝ)^n) hh) b hb

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.ito_approximation_from_essential_bounds
