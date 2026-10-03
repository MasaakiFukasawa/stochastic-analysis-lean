import Chapter3IncrementEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- The sum of actual stopped-increment second moments is bounded by E Q_t.
The equality to compensator increments and their integrability are derived
from the original local martingale and square-defect construction. -/
theorem actual_partition_increment_energy_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Q : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hQ : LocalCovarianceWitness P F X X Q)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτmono : ∀ ω, Monotone (fun j => τ j ω)) (hτtop : ∀ j ω, τ j ω < ⊤)
    (hτ0 : ∀ ω, τ 0 ω = ⊥)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω‖ ≤ δ)
    (t : ClosedTime T) (ht : t < ⊤) (hiQ : Integrable (Q t) P) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      ∫ ω, (X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)^2 ∂P) ≤
      ∫ ω, Q t ω ∂P := by
  let D := fun j r ω => X (min (τ (j+1) ω) r) ω-X (min (τ j ω) r) ω
  let B := fun j r ω => Q (min (τ (j+1) ω) r) ω-Q (min (τ j ω) r) ω
  have hd (j) := stopped_increment_bounded P F hF hle X hX (τ j) (τ (j+1))
    (hτ j) (hτ (j+1)) (fun ω => hτmono ω (Nat.le_succ j)) (hτtop (j+1)) δ (hb j)
  have hr (j) := actual_increment_defect_m2 P F hF hle hnull X Q hX hQ (τ j) (τ (j+1))
    (hτ j) (hτ (j+1)) (fun ω => hτmono ω (Nat.le_succ j)) (hτtop (j+1)) δ hδ (hb j)
  have he (j) := increment_energy_of_square_defect P F hle (D j) (B j) (hd j).1.moment (hr j) t
  change (∑ j ∈ Finset.range N, ∫ ω, D j t ω^2 ∂P) ≤ _
  simp_rw [fun j => (he j).2]
  rw [← integral_finsetSum _ (fun j _ => (he j).1)]
  apply integral_mono_ae (integrable_finsetSum _ (fun j _ => (he j).1)) hiQ
  filter_upwards [local_quadratic_variation_monotone P F hF hle hnull X Q hX hQ,
    local_quadratic_variation_initial P F X Q hX hQ] with ω hm hz
  change (∑ j ∈ Finset.range N, (Q (min (τ (j+1) ω) t) ω-Q (min (τ j ω) t) ω)) ≤ Q t ω
  rw [finite_increment_telescoping (fun s => Q s ω) (fun j => min (τ j ω) t) N]
  simp only [hτ0,min_bot_left,hz,Pi.zero_apply,sub_zero]
  exact hm ((min_le_right _ _).trans_lt ht) ht (min_le_right _ _)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.actual_partition_increment_energy_bound
