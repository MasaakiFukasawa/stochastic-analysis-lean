import Chapter3QuadraticApproximationProperty
import Chapter3StoppedOscillation

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Apply the bounded theorem to an actual stopped local martingale and
a clipped continuous weight. Stopping, covariance, integrability and
oscillation hypotheses are derived from the original data. -/
theorem stopped_clipped_quadratic_approximation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (hHm : ∀ t, t < ⊤ → Measurable[F t] (H t))
    (hHc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => H s ω) t)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → ℕ → Ω → ClosedTime T)
    (hτ : ∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t})
    (hτmono : ∀ n ω, Monotone (fun j => τ n j ω))
    (hτtop : ∀ n j ω, τ n j ω < ⊤) (hτ0 : ∀ n ω, τ n 0 ω = ⊥)
    (hcofinal : ∀ n ω b, b < ⊤ → ∃ N, b < τ n N ω)
    (hb : ∀ n j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ n (j+1) ω) t) ω-X (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n)
    (hHosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |H (τ n j ω) ω-H t ω| ≤ (1/2:ℝ)^n)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) (L : ℝ)
    (hQb : ∀ᵐ ω ∂P, ∀ t, 0 ≤ Q (min (σ ω) t) ω ∧ Q (min (σ ω) t) ω ≤ L)
    (K : ℝ) (hK : 0 ≤ K)
    (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T) :
    ∀ᵐ ω ∂P, QuadraticPathApproximation
      (fun t => X (min (σ ω) t) ω) (fun t => Q (min (σ ω) t) ω)
      (fun t => intervalClamp (-K) K (by linarith) (H (min (σ ω) t) ω))
      (fun n j => τ n j ω) d hd := by
  let Hs := fun t ω => intervalClamp (-K) K (by linarith) (H (min (σ ω) t) ω)
  have hHs := open_continuous_adapted_stopped_regular F hF H hHm hHc c hcm hct hcc σ hσ hσt
  have hHsm (t) : Measurable[F t] (Hs t) :=
    (intervalClamp_continuous (-K) K (by linarith)).measurable.comp (hHs.1 t)
  have hHsc (ω) : Continuous (fun t => Hs t ω) :=
    (intervalClamp_continuous (-K) K (by linarith)).comp (hHs.2 ω)
  have hHsb : ∀ᵐ ω ∂P, ∀ t, |Hs t ω| ≤ K :=
    .of_forall (fun ω t => symmetric_clamp_abs_bound K hK _)
  have hXs := hX.stopped P F hF hle σ hσ
  have hQs := hQ.stopped P F hF hle σ hσ
  have hQreg := hQ.stopped_regular P F hF hle hX hX σ hσ hσt
  have hQi : Integrable (fun ω => Q (min (σ ω) (realTimeClamp d)) ω) P := by
    have hm : AEStronglyMeasurable (fun ω => Q (min (σ ω) (realTimeClamp d)) ω) P :=
      ((hQreg.1 (realTimeClamp d)).mono (hle _) le_rfl).aestronglyMeasurable
    have hm2 : MemLp (fun ω => Q (min (σ ω) (realTimeClamp d)) ω) 2 P := by
      apply MemLp.of_bound hm L
      filter_upwards [hQb] with ω hω
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hω _).1] using (hω (realTimeClamp d)).2
    exact hm2.integrable (by norm_num)
  have hinc (n j) : ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (σ ω) (min (τ n (j+1) ω) t)) ω-X (min (σ ω) (min (τ n j ω) t)) ω‖ ≤ (1/2:ℝ)^n := by
    filter_upwards [hb n j] with ω hω
    intro t
    simpa only [min_left_comm] using hω (min (σ ω) t)
  have hosc : ∀ᵐ ω ∂P, ∀ n j t, τ n j ω ≤ t → t ≤ τ n (j+1) ω →
      |Hs (τ n j ω) ω-Hs t ω| ≤ (1/2:ℝ)^n := by
    filter_upwards [hHosc] with ω hω
    intro n j t hj ht
    exact (interval_clamp_abs_sub_le (-K) K (by linarith) _ _).trans
      (stopped_interval_oscillation (fun t => H t ω) (fun j => τ n j ω) (σ ω) ((1/2:ℝ)^n)
        (pow_nonneg (by norm_num) n) (hω n) j t hj ht)
  exact bounded_continuous_quadratic_approximation P F hF hle hnull _ _ Hs hXs hQs τ
    hτ hτmono hτtop hτ0 hcofinal K hK hinc hHsm hHsc hHsb d hd hdT hQi hosc

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.stopped_clipped_quadratic_approximation
