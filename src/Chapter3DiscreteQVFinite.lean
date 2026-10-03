import Chapter3WeightedPartition
import Chapter3IncrementProcess

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The square-defect appearing in the manuscript, with j starting at zero
so the two endpoints are τ_j and τ_(j+1). -/
noncomputable def partitionDefect {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X Q : ClosedTime T → Ω → ℝ) (τ : ℕ → Ω → ClosedTime T)
    (j : ℕ) (t : ClosedTime T) (ω : Ω) : ℝ :=
    (X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)^2-
      (Q (min (τ (j+1) ω) t) ω-Q (min (τ j ω) t) ω)

/-- The finite-sum identity in prop:qcv is proved for the actual X and its
actual quadratic variation Q. Neither the M2 property of the square defects
nor their orthogonality is a hypothesis of this theorem. -/
theorem discrete_qv_finite_energy
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
    (hAb : ∀ j, MemLp (A j) ∞ P) (N : ℕ) :
    (∫ ω, (∑ j ∈ Finset.range N, A j ω*partitionDefect X Q τ j ⊤ ω)^2 ∂P) =
      ∑ j ∈ Finset.range N, ∫ ω, (A j ω*partitionDefect X Q τ j ⊤ ω)^2 ∂P := by
  have hY (j) : ContinuousM2Witness P F (partitionDefect X Q τ j) :=
    actual_increment_defect_m2 P F hF hle hnull X Q hX hQ (τ j) (τ (j+1))
      (hτ j) (hτ (j+1)) (fun ω => hτmono ω (Nat.le_succ j)) (hτtop (j+1)) δ hδ (hb j)
  apply weighted_partition_energy P F hF hle (partitionDefect X Q τ) hY τ hτ _ _ A hA hAb N
  · intro j ω t ht
    simp only [partitionDefect,min_eq_right ht,
      min_eq_right (ht.trans (hτmono ω (Nat.le_succ j))),sub_self,zero_pow (by decide : 2 ≠ 0)]
  · intro i j hij ω
    simp only [partitionDefect,min_eq_left (hτmono ω hij.le),
      min_eq_left (hτmono ω (Nat.succ_le_of_lt hij)),min_top_right]

/-- The other stochastic step in the finite-sum estimate: the actual weighted
error sum is continuous M2, so Doob is applicable to it. -/
theorem discrete_qv_finite_sum_m2
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
    (hAb : ∀ j, MemLp (A j) ∞ P) (N : ℕ) :
    ContinuousM2Witness P F
      (fun t ω => ∑ j ∈ Finset.range N, A j ω*partitionDefect X Q τ j t ω) := by
  apply finite_sum_m2 P F (Finset.range N)
  intro j hj
  apply bounded_stopped_weight_m2 P F hF hle (partitionDefect X Q τ j)
    (actual_increment_defect_m2 P F hF hle hnull X Q hX hQ (τ j) (τ (j+1))
      (hτ j) (hτ (j+1)) (fun ω => hτmono ω (Nat.le_succ j)) (hτtop (j+1)) δ hδ (hb j))
    (τ j) (hτ j) _ (A j) (hA j) (hAb j)
  intro ω t ht
  simp only [partitionDefect,min_eq_right ht,
    min_eq_right (ht.trans (hτmono ω (Nat.le_succ j))),sub_self,zero_pow (by decide : 2 ≠ 0)]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.discrete_qv_finite_energy
#print axioms Asakura.Chapter3Complete.discrete_qv_finite_sum_m2
