import Chapter3DiscreteIntegralCovariance
import Chapter3PartitionStepSignedIntegral
import Chapter3SupportedCovarianceMeasure
import Chapter2ItoCovarianceCharacterization

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The actual discrete sum satisfies the defining covariance formula of
the Ito integral of its partition step integrand. No integral identity or
convergence statement is assumed. -/
theorem discrete_integral_ito_formula
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X H : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (τ : ℕ → Ω → ClosedTime T)
    (hτ : ∀ j t, MeasurableSet[F t] {ω | τ j ω ≤ t})
    (hτm : ∀ ω, Monotone (fun j => τ j ω)) (hτt : ∀ j ω, τ j ω < ⊤)
    (hτc : ∀ ω t, t < ⊤ → ∃ j, t < τ j ω)
    (hA : ∀ j, Measurable[writtenStoppedSpace m F (τ j) (hτ j)] (fun ω => H (τ j ω) ω))
    (hAb : ∀ j, MemLp (fun ω => H (τ j ω) ω) ∞ P) :
    ItoCovarianceFormula P F X
      (fun z => partitionStep (fun t => H t z.1) (fun j => τ j z.1) (realTimeClamp z.2))
      (fun t ω => ∑' j, H (τ j ω) ω*(X (min (τ (j+1) ω) t) ω-X (min (τ j ω) t) ω)) := by
  intro Y C hY hC
  obtain ⟨E,hE,he⟩ := discrete_integral_covariance P F hF hle hnull X Y C hX hY hC
    c hcm hct hcc τ hτ hτm hτt hτc (fun j ω => H (τ j ω) ω) hA hAb
  refine ⟨E,hE,?_⟩
  intro d hd hdT
  obtain ⟨ν,hν,hs⟩ := supported_covariance_measure P F hF hle hnull X Y C hX hY hC d hd hdT
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  refine ⟨ν,hν,?_,?_,?_⟩
  · filter_upwards [hs] with ω hsω
    have hlo : ∀ᵐ r ∂(ν ω).totalVariation, 0 < r := hsω.mono (fun _ h => h.1)
    rw [ae_iff] at hlo
    simpa only [not_lt, Iic] using hlo
  · filter_upwards [hs] with ω hsω
    obtain ⟨N,hN⟩ := hτc ω (realTimeClamp d) hdt
    exact partition_step_signed_integrable d hd hdT.le (fun t => H t ω) (fun j => τ j ω)
      (hτm ω) N hN.le (ν ω) hsω
  · filter_upwards [hs,he _ hdt] with ω hsω heω
    obtain ⟨N,hN⟩ := hτc ω (realTimeClamp d) hdt
    rw [heω,partition_sum_truncates_before_endpoint (fun j => τ j ω) (hτm ω)
      (fun t => C t ω) (fun j => H (τ j ω) ω) N _ hN.le,
      partition_step_signed_integral d hd hdT.le (fun t => H t ω) (fun j => τ j ω) (hτm ω) N hN.le (ν ω) hsω]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hν ω _ _ (finitePrefixTime d hd (τ j ω)).property.1
      (finite_prefix_time_mono d hd (hτm ω (Nat.le_succ j))),
      finite_prefix_time_clamp d hd hdT.le,finite_prefix_time_clamp d hd hdT.le]
    simp only [min_assoc,min_left_comm,min_self,min_comm,Nat.succ_eq_add_one]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.discrete_integral_ito_formula
