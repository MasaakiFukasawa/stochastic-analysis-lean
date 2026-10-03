import Chapter3DiscreteQVAtTime
import Chapter3PartitionEnergyBound
import Chapter3EnergyBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The finite quantitative estimate in prop:qcv, with every stochastic
premise discharged for the original X, Q and stopping partition. In the
manuscript δ=2^(-n); the bound is uniform in the truncation N. -/
theorem actual_discrete_qv_error_energy
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
    (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hb : ∀ j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω‖ ≤ δ)
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P)
    (hAK : ∀ j, ∀ᵐ ω ∂P, |A j ω| ≤ K)
    (t : ClosedTime T) (ht : t < ⊤) (hiQ : Integrable (Q t) P) (N : ℕ) :
    (∫ ω, (∑ j ∈ Finset.range N, A j ω*partitionDefect X Q τ j t ω)^2 ∂P) ≤
      4*δ^2*K^2*(∫ ω, Q t ω ∂P) := by
  let e := fun j => ∫ ω, (X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)^2 ∂P
  have he (j) : 0 ≤ e j := integral_nonneg fun ω => sq_nonneg _
  have hY (j) := actual_increment_defect_m2 P F hF hle hnull X Q hX hQ (τ j) (τ (j+1))
    (hτ j) (hτ (j+1)) (fun ω => hτmono ω (Nat.le_succ j)) (hτtop (j+1)) δ hδ (hb j)
  have hnorm (j) : eLpNorm (partitionDefect X Q τ j t) 2 P ≤
      ENNReal.ofReal (2*δ*Real.sqrt (e j)) :=
    (stopped_increment_lemma P F hF hle hnull X Q hX hQ (τ j) (τ (j+1))
      (hτ j) (hτ (j+1)) (fun ω => hτmono ω (Nat.le_succ j)) (hτtop (j+1)) δ hδ (hb j)).2.2 t ht
  rw [discrete_qv_finite_energy_at_time P F hF hle hnull X Q hX hQ τ hτ hτmono hτtop
    δ hδ hb A hA hAb N t]
  have hterm (j) : (∫ ω, (A j ω*partitionDefect X Q τ j t ω)^2 ∂P) ≤
      K^2*(4*δ^2*e j) := by
    apply (weighted_square_integral_bound P (A j) (partitionDefect X Q τ j t)
      (hAb j) ((hY j).moment t) K hK (hAK j)).trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
    have h := square_integral_le_of_l2_bound P _ ((hY j).moment t) (2*δ*Real.sqrt (e j))
      (mul_nonneg (mul_nonneg (by norm_num) hδ) (Real.sqrt_nonneg _)) (hnorm j)
    have heq : (2*δ*Real.sqrt (e j))^2 = 4*δ^2*e j := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (he j)]
      ring
    simpa only [heq,partitionDefect] using h
  calc
    _ ≤ ∑ j ∈ Finset.range N, K^2*(4*δ^2*e j) := Finset.sum_le_sum fun j _ => hterm j
    _ = (4*δ^2*K^2)*(∑ j ∈ Finset.range N, e j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (actual_partition_increment_energy_bound P F hF hle hnull X Q hX hQ τ hτ hτmono hτtop hτ0
        δ hδ hb t ht hiQ N)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg δ)) (sq_nonneg K))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.actual_discrete_qv_error_energy
