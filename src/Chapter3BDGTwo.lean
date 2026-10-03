import Chapter3LocalEnergyMaximal

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The p=2 BDG argument for integrable quadratic variation, including its
exact lower constant and the Doob upper constant. -/
theorem bdg_two_integrable_variation
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (hCi : Integrable (fun ω => C (σ ω) ω) P) :
    ∃ hc : ∀ ω, Continuous (fun t => X (min (σ ω) t) ω),
      MemLp (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) 2 P ∧
      (ENNReal.ofReal (∫ ω, C (σ ω) ω ∂P))^(1/(2:ℝ)) ≤
        eLpNorm (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) 2 P ∧
      eLpNorm (continuousPath (fun t ω => X (min (σ ω) t) ω) hc) 2 P ≤
        2*(ENNReal.ofReal (∫ ω, C (σ ω) ω ∂P))^(1/(2:ℝ)) := by
  obtain ⟨hc,hp,hu⟩ := local_stop_path_memLp_of_integrable_variation P F hF hle hnull X C hX hC σ hσ hσtop hCi
  obtain ⟨h1,h2⟩ := stopped_local_M2_equivalences P F hF hle hnull X C hX hC σ hσ hσtop
  have hM2 := h2.mp (h1.mp hCi)
  have henergy := (stopped_M2_energy P F hF hle hnull X C hX hC σ hσ hσtop hM2).2
  have hm : MemLp (fun ω => X (σ ω) ω) 2 P := by
    simpa only [min_top_right] using hM2.moment ⊤
  refine ⟨hc,hp,?_,hu⟩
  rw [← henergy,← real_eLpNorm_two_energy P _ hm]
  apply eLpNorm_mono_ae hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    have h := (continuousPath (fun t ω => X (min (σ ω) t) ω) hc ω).norm_coe_le_norm ⊤
    simpa only [continuousPath,ContinuousMap.coe_mk,min_top_right] using h)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.bdg_two_integrable_variation
