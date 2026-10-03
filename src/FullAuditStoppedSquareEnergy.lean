import FullAuditPartitionEnergy
import FullAuditStoppedMeanExercise

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

theorem deterministic_stopped_space {Ω ι : Type*} {m : MeasurableSpace Ω} [LinearOrder ι]
    (F : ι → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m) (t : ι)
    (ht : ∀ s, MeasurableSet[F s] {ω : Ω | t ≤ s}) :
    writtenStoppedSpace m F (fun _ => t) ht = F t := by
  apply le_antisymm
  · intro A hA
    simpa only [le_refl,setOf_true,inter_univ] using hA.2 t
  · intro A hA
    refine ⟨hle t _ hA,fun s => ?_⟩
    by_cases hts : t ≤ s
    · simpa only [hts,setOf_true,inter_univ] using hF hts _ hA
    · simp only [hts,setOf_false,inter_empty]; exact @MeasurableSet.empty Ω (F s)

/-- Evaluate the previously checked square-defect martingale at an actual
 stopping time, retaining all integrability needed to split the expectation. -/
theorem stopped_partition_energy {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (h2 : ∀ t, MemLp (X t) 2 P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0)
    (π : ℕ → ClosedTime T) (hπ : Monotone π) (h0 : π 0 = ⊥) (N : ℕ) (hN : π N = ⊤)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hsq : Integrable (fun ω => X (τ ω) ω ^ 2) P) :
    Integrable (fun ω => partitionSquares X π N (τ ω) ω) P ∧
      (∫ ω, partitionSquares X π N (τ ω) ω ∂P) = ∫ ω, X (τ ω) ω ^ 2 ∂P := by
  let Y := fun t ω => X t ω ^ 2-partitionSquares X π N t ω
  have hmY (t) : Measurable[F t] (Y t) := (partition_square_defect_adapted_integrable P F hF X hm h2 π N t).1
  have hiY (t) : Integrable (Y t) P := (partition_square_defect_adapted_integrable P F hF X hm h2 π N t).2
  have hcY := partition_square_defect_continuous X hc π N
  have hzY : Y ⊥ =ᵐ[P] 0 := by
    filter_upwards [hz] with ω hω
    simp only [Y,hω,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),partition_squares_initial,sub_zero]
  have hmYmart := partition_square_martingale_written P F hF hle X hm h2 hmart π hπ h0 N hN
  have h := (zero_stopped_mean_exercise P (Fact.out : 0 ≤ T) F hF hle Y hmY hiY
    (fun ω t => (hcY ω).continuousAt.continuousWithinAt) hzY).mp hmYmart τ hτ
  have hiQ : Integrable (fun ω => partitionSquares X π N (τ ω) ω) P := by
    convert hsq.sub h.1 using 1
    ext ω; simp only [Pi.sub_apply,Y]; ring
  refine ⟨hiQ,?_⟩
  have hmean := h.2
  change (∫ ω, X (τ ω) ω ^ 2-partitionSquares X π N (τ ω) ω ∂P) = 0 at hmean
  rw [integral_sub hsq hiQ] at hmean
  linarith

/-- Optional sampling at a deterministic observation time identifies the
 entire stopped process with the conditional expectations of its terminal value. -/
theorem stopped_value_conditional {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, Integrable (X t) P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hmart : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) (t : ClosedTime T) :
    P[(fun ω => X (τ ω) ω) | F t] =ᵐ[P] fun ω => X (min t (τ ω)) ω := by
  have ht (s : ClosedTime T) : MeasurableSet[F s] {ω : Ω | t ≤ s} := by
    by_cases h : t ≤ s <;> simp [h]
  have h := continuous_optional_sampling_written P (Fact.out : 0 ≤ T) F hF hle X hm hi
    (fun ω t => (hc ω).continuousAt.continuousWithinAt) hmart τ (fun _ => t) hτ ht
  rw [deterministic_stopped_space F hF hle t ht] at h
  simpa only [min_comm] using h

end Asakura.FullAudit
