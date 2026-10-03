import Chapter3StoppedIncrementCovariance
import Chapter2ElementaryFiniteSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Covariance of the finite discrete integral with any local martingale.
Every stopping coefficient is handled by the weighted local-martingale
lemma; the resulting compensator is the literal weighted sum of increments. -/
theorem finite_discrete_integral_covariance
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
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P) (N : ℕ) :
    LocalMProcessWitness P F
      (fun t ω => ∑ j ∈ Finset.range N, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)) ∧
    LocalCovarianceWitness P F
      (fun t ω => ∑ j ∈ Finset.range N, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)) Y
      (fun t ω => ∑ j ∈ Finset.range N, A j ω*(C (min (τ (j+1) ω) t) ω-C (min (τ j ω) t) ω)) := by
  let D := fun j t ω => X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω
  let E := fun j t ω => C (min (τ (j+1) ω) t) ω-C (min (τ j ω) t) ω
  have hD (j) : LocalMProcessWitness P F (D j) := by
    have hs := hX.stopped P F hF hle (τ j) (hτ j)
    have ht := hX.stopped P F hF hle (τ (j+1)) (hτ (j+1))
    convert (hs.smul P F (-1)).add P F hF hle ht using 1
    funext t ω
    dsimp only [D]
    ring
  have hz (Z : ClosedTime T → Ω → ℝ) (j ω t) (ht : t ≤ τ j ω) :
      Z (min (τ (j+1) ω) t) ω-Z (min (τ j ω) t) ω = 0 := by
    rw [min_eq_right ht,min_eq_right (ht.trans (hτm ω (Nat.le_succ j))),sub_self]
  have hDC (j) := actual_stopped_increment_covariance P F hF hle hnull X Y C hX hY hC
    c hcm hct hcc (τ j) (τ (j+1)) (hτ j) (hτ (j+1)) (hτt j) (hτt (j+1))
  have hW (j) := bounded_stopped_weight_local P F hF hle (D j) (hD j) (τ j) (hτ j)
    (hz X j) (A j) (hA j) (hAb j)
  have hWC (j) := bounded_stopped_weight_covariance P F hF hle (D j) Y (E j) (hDC j)
    (τ j) (hτ j) (hz X j) (hz C j) (A j) (hA j) (hAb j)
  have hzero : LocalMProcessWitness P F (fun _ _ => 0) := by
    simpa only [zero_mul] using hX.smul P F 0
  have hc0 : LocalCovarianceWitness P F (fun _ _ => 0) Y (fun _ _ => 0) := by
    refine ⟨?_,?_⟩
    · simpa only [zero_mul,sub_self] using hzero
    · simpa only [zero_mul] using hC.variation.smul F 0
  exact ⟨local_process_finset_sum P F hF hle (Finset.range N) _ (fun j _ => hW j) hzero,
    local_covariance_finset_sum P F hF hle (Finset.range N) _ _ Y (fun j _ => hWC j) hc0⟩

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.finite_discrete_integral_covariance
