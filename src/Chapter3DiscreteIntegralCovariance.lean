import Chapter3FiniteDiscreteCovariance
import Chapter3DiscreteIntegralLocalMartingale
import Chapter3DiscreteTruncationProbability
import Chapter2CovarianceLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The covariance of the actual countable discrete integral is the
countable weighted covariance sum at every finite time. Both limits in
probability are derived, rather than supplied as assumptions. -/
theorem discrete_integral_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτm : ∀ ω, Monotone (fun j => τ j ω)) (hτt : ∀ j ω, τ j ω < ⊤)
    (hτc : ∀ ω t, t < ⊤ → ∃ j, t < τ j ω)
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P) :
    let R := fun t ω => ∑' j, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)
    ∃ E, LocalCovarianceWitness P F R Y E ∧ ∀ b, b < ⊤ →
      E b =ᵐ[P] fun ω => ∑' j, A j ω*(C (min (τ (j+1) ω) b) ω-C (min (τ j ω) b) ω) := by
  intro R
  have hR := discrete_integral_local_martingale P F hF hle X hX τ hτ hτm hτt hτc A hA hAb
  obtain ⟨E,hE⟩ := local_covariance_witness_exists P F hF hle hnull R Y hR hY
  obtain ⟨B,hB⟩ := local_covariance_witness_exists P F hF hle hnull Y Y hY hY
  refine ⟨E,hE,?_⟩
  intro b hb
  let Rn := fun n t ω => ∑ j ∈ Finset.range n, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)
  let Dn := fun n t ω => ∑ j ∈ Finset.range n, A j ω*(C (min (τ (j+1) ω) t) ω-C (min (τ j ω) t) ω)
  have hf n := finite_discrete_integral_covariance P F hF hle hnull X Y C hX hY hC
    c hcm hct hcc τ hτ hτm hτt A hA hAb n
  have hp := covariance_probability_continuity P F hF hle hnull Rn Dn R Y B E
    (fun n => (hf n).1) hR hY (fun n => (hf n).2) hB hE b hb
    (fun ε hε => (discrete_sum_truncation_probability P F hF hle τ hτ hτm hτc X A b hb ε hε).1)
  have hq : TendstoInMeasure P (fun n => Dn n b) atTop (E b) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using hp
  have hs : TendstoInMeasure P (fun n => Dn n b) atTop
      (fun ω => ∑' j, A j ω*(C (min (τ (j+1) ω) b) ω-C (min (τ j ω) b) ω)) := by
    rw [tendstoInMeasure_iff_norm]
    simpa only [Real.norm_eq_abs] using
      (fun ε hε => (discrete_sum_truncation_probability P F hF hle τ hτ hτm hτc C A b hb ε hε).2)
  exact tendstoInMeasure_ae_unique hq hs

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.discrete_integral_covariance
