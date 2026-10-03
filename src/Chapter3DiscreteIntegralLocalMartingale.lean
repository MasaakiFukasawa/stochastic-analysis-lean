import Chapter3WeightedLocalMartingale
import Chapter3OrthogonalSum

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The actual infinite discrete integral is a local martingale.
A common localizer cuts both the integrator and the number of active
partition intervals; each resulting finite sum is proved to be M2. -/
theorem discrete_integral_local_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτm : ∀ ω, Monotone (fun j => τ j ω))
    (hτt : ∀ j ω, τ j ω < ⊤)
    (hτc : ∀ ω t, t < ⊤ → ∃ j, t < τ j ω)
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P) :
    LocalMProcessWitness P F
      (fun t ω => ∑' j, A j ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)) := by
  obtain ⟨ρ,hρ,hρm,hρt,hρc,hXρ⟩ := hX.localizers
  let κ := fun n ω => min (τ n ω) (ρ n ω)
  have hκ (n) := (written_stopping_min_max F (τ n) (ρ n) (hτ n) (hρ n)).1
  have hκm (ω) : Monotone (fun n => κ n ω) := (hτm ω).min (hρm ω)
  have hκt (n ω) : κ n ω < ⊤ := (min_le_left _ _).trans_lt (hτt n ω)
  have hκc (ω) := (common_localizers_cofinal (fun n => τ n ω) (fun n => ρ n ω)
    (hτm ω) (hρm ω) (hτc ω) (hρc ω)).2
  apply m2_localization_implies_local P F hF hle _ κ hκ hκm hκt hκc
  intro n
  let D := fun j t ω => X (min (ρ n ω) (min (τ (j+1) ω) t)) ω-
    X (min (ρ n ω) (min (τ j ω) t)) ω
  have hD (j) : ContinuousM2Witness P F (D j) := by
    have hu := continuous_m2_stopped P F hF hle _ (hXρ n).1 (τ (j+1)) (hτ (j+1))
    have hv := continuous_m2_stopped P F hF hle _ (hXρ n).1 (τ j) (hτ j)
    convert (hv.smul P F (-1)).add P F hu using 1
    funext t ω
    simp only [D,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hz (j ω t) (ht : t ≤ τ j ω) : D j t ω = 0 := by
    simp only [D,min_eq_right ht,min_eq_right (ht.trans (hτm ω (Nat.le_succ j))),sub_self]
  have hW (j) := bounded_stopped_weight_m2 P F hF hle (D j) (hD j) (τ j) (hτ j)
    (hz j) (A j) (hA j) (hAb j)
  have hs := finite_sum_m2 P F (Finset.range n) (fun j t ω => A j ω*D j t ω) (fun j _ => hW j)
  have he : (fun t ω => ∑' j, A j ω*
      (X (min (τ (j+1) ω) (min (κ n ω) t)) ω-X (min (τ j ω) (min (κ n ω) t)) ω)) =
      (fun t ω => ∑ j ∈ Finset.range n, A j ω*D j t ω) := by
    funext t ω
    rw [tsum_eq_sum (s := Finset.range n)]
    · apply Finset.sum_congr rfl
      intro j hj
      have hm (i : ℕ) (hi : i ≤ n) : min (τ i ω) (min (κ n ω) t) = min (ρ n ω) (min (τ i ω) t) := by
        dsimp only [κ]
        rw [min_assoc (τ n ω) (ρ n ω) t,← min_assoc (τ i ω) (τ n ω) (min (ρ n ω) t),
          min_eq_left (hτm ω hi),min_left_comm]
      rw [hm (j+1) (by have := Finset.mem_range.mp hj; omega),
        hm j (Nat.le_of_lt (Finset.mem_range.mp hj))]
    · intro j hj
      have hnj : n ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
      have htj : min (κ n ω) t ≤ τ j ω :=
        (min_le_left _ _).trans ((min_le_left _ _).trans (hτm ω hnj))
      rw [min_eq_right htj,min_eq_right (htj.trans (hτm ω (Nat.le_succ j))),sub_self,mul_zero]
  rw [he]
  exact hs

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.discrete_integral_local_martingale
