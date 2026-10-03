import Chapter3DiscreteQVErrorEnergy
import Chapter3LocallyFiniteDoob
import Chapter3LocallyFinitePartition
import Chapter3EnergyToNorm

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The full stochastic maximal-error estimate of prop:qcv, before the
Stieltjes Riemann error and removal of localization. The infinite sum,
its continuous path, its measurability and the Fatou--Doob estimate are all
derived from the actual local martingale, QV and stopping partition. -/
theorem actual_discrete_qv_maximal_error
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
    (hcofinal : ∀ ω b, b < ⊤ → ∃ N, b < τ N ω)
    (δ K : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hb : ∀ j, ∀ᵐ ω ∂P, ∀ t,
      ‖X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω‖ ≤ δ)
    (A : ℕ → Ω → ℝ)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (A j))
    (hAb : ∀ j, MemLp (A j) ∞ P)
    (hAK : ∀ j, ∀ᵐ ω ∂P, |A j ω| ≤ K)
    (b : ClosedTime T) (hbT : b < ⊤) (hiQ : Integrable (Q b) P) :
    let E := fun t ω => ∑' j, A j ω*partitionDefect X Q τ j (min b t) ω
    ∃ hc : ∀ ω, Continuous (fun t => E t ω),
      AEStronglyMeasurable (continuousPath E hc) P ∧
      eLpNorm (continuousPath E hc) 2 P ≤
        ENNReal.ofReal (4*δ*K*Real.sqrt (∫ ω, Q b ω ∂P)) := by
  intro E
  let S := fun N t ω => ∑ j ∈ Finset.range N, A j ω*partitionDefect X Q τ j (min b t) ω
  have hbstop : ∀ r, MeasurableSet[F r] {ω : Ω | b ≤ r} := by
    intro r
    by_cases h : b ≤ r <;> simp [h]
  have hS (N) : ContinuousM2Witness P F (S N) :=
    continuous_m2_stopped P F hF hle _
      (discrete_qv_finite_sum_m2 P F hF hle hnull X Q hX hQ τ hτ hτmono hτtop
        δ hδ hb A hA hAb N) (fun _ => b) hbstop
  have hstab (ω) : ∃ N, ∀ n, N ≤ n → ∀ t, S n t ω = E t ω := by
    obtain ⟨N,hN⟩ := partition_defect_sum_locally_finite (fun j => τ j ω) (hτmono ω)
      (hcofinal ω) (fun t => X t ω) (fun t => Q t ω) (fun j => A j ω) b hbT
    refine ⟨N,?_⟩
    intro n hn t
    exact (hN n hn (min b t) (min_le_left _ _)).symm
  have hQ0 : 0 ≤ ∫ ω, Q b ω ∂P := by
    simpa only [Finset.range_zero,Finset.sum_empty] using
      actual_partition_increment_energy_bound P F hF hle hnull X Q hX hQ τ hτ hτmono hτtop hτ0
        δ hδ hb b hbT hiQ 0
  let C := 2*δ*K*Real.sqrt (∫ ω, Q b ω ∂P)
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hδ) hK) (Real.sqrt_nonneg _)
  have hC (N) : eLpNorm (S N ⊤) 2 P ≤ ENNReal.ofReal C := by
    apply l2_bound_of_square_integral_le P _ ((hS N).moment ⊤) C hC0
    have hh := actual_discrete_qv_error_energy P F hF hle hnull X Q hX hQ τ hτ hτmono hτtop hτ0
      δ K hδ hK hb A hA hAb hAK b hbT hiQ N
    have he : C^2 = 4*δ^2*K^2*(∫ ω, Q b ω ∂P) := by
      dsimp only [C]
      rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hQ0]
      ring
    simpa only [S,min_top_right,he] using hh
  obtain ⟨hc,hm,hn⟩ := locally_finite_m2_sum_maximal_bound P F hF hle S hS E hstab (ENNReal.ofReal C) hC
  refine ⟨hc,hm,hn.trans_eq ?_⟩
  calc
    2*ENNReal.ofReal C = ENNReal.ofReal (2*C) := by
      conv_rhs => rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [ENNReal.ofReal_ofNat]
    _ = _ := by congr 1; dsimp only [C]; ring

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.actual_discrete_qv_maximal_error
