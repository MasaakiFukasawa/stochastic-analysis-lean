import Chapter2IntegrableVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤)

include hF hle hnull hX hC hσ hσtop

/-- The equivalence of finite quadratic-variation expectation, an L2
pathwise supremum, and stopped M2 membership in prop244. -/
theorem stopped_local_M2_equivalences :
    (Integrable (fun ω => C (σ ω) ω) P ↔
      ∃ B : Ω → ℝ, MemLp B 2 P ∧ ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ ω) t) ω‖ ≤ B ω) ∧
    ((∃ B : Ω → ℝ, MemLp B 2 P ∧ ∀ᵐ ω ∂P, ∀ t, ‖X (min (σ ω) t) ω‖ ≤ B ω) ↔
      ContinuousM2Witness P F (fun t ω => X (min (σ ω) t) ω)) := by
  constructor
  · constructor
    · intro hi
      obtain ⟨hc,hp,_⟩ := local_stop_path_memLp_of_integrable_variation
        P F hF hle hnull X C hX hC σ hσ hσtop hi
      refine ⟨fun ω => ‖continuousPath (fun t ω => X (min (σ ω) t) ω) hc ω‖,hp.norm,?_⟩
      exact .of_forall fun ω t => (continuousPath _ hc ω).norm_coe_le_norm t
    · rintro ⟨B,hB,hb⟩
      exact (stopped_local_energy_of_square_integrable_bound P F hF hle hnull X C hX hC σ hσ hσtop B hB hb).1
  · constructor
    · rintro ⟨B,hB,hb⟩
      exact local_stop_is_m2_of_square_integrable_bound P F hF hle X hX σ hσ hσtop B hB hb
    · intro hY
      have hp := continuous_martingale_path_memLp P F hF hle _
        hY.adapted hY.moment hY.path hY.martingale
      refine ⟨fun ω => ‖continuousPath _ hY.path ω‖,hp.norm,?_⟩
      exact .of_forall fun ω t => (continuousPath _ hY.path ω).norm_coe_le_norm t

/-- The energy equality belonging to assertion (iii) of prop244. -/
theorem stopped_M2_energy
    (hY : ContinuousM2Witness P F (fun t ω => X (min (σ ω) t) ω)) :
    Integrable (fun ω => C (σ ω) ω) P ∧
    (∫ ω, X (σ ω) ω ^ 2 ∂P) = ∫ ω, C (σ ω) ω ∂P := by
  obtain ⟨B,hB,hb⟩ := (stopped_local_M2_equivalences P F hF hle hnull X C hX hC σ hσ hσtop).2.mpr hY
  exact stopped_local_energy_of_square_integrable_bound P F hF hle hnull X C hX hC σ hσ hσtop B hB hb

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.stopped_local_M2_equivalences
#print axioms Asakura.Chapter2Complete.stopped_M2_energy
