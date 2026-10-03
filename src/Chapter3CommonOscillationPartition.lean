import Chapter3FiniteVectorOscillationPartition
import Chapter3ContinuousAdaptedWeights

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- A single stopping partition simultaneously satisfies the manuscript's
essential-supremum condition for every member of any finite family. -/
theorem common_oscillation_partition
    {J Ω : Type*} [Fintype J] [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (hle : ∀ t, F t ≤ ‹MeasurableSpace Ω›)
    (X : J → ClosedTime T → Ω → ℝ)
    (hm : ∀ i t, t < ⊤ → Measurable[F t] (X i t))
    (hX : ∀ i ω t, t < ⊤ → ContinuousAt (fun s => X i s ω) t)
    (c : ℕ → ClosedTime T) (hc : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n) :
    ∃ τ : ℕ → ℕ → Ω → ClosedTime T,
      (∀ n ω, τ n 0 ω = ⊥) ∧
      (∀ n j t, MeasurableSet[F t] {ω | τ n j ω ≤ t}) ∧
      (∀ n ω, Monotone (fun j => τ n j ω)) ∧
      (∀ n j ω, τ n j ω < ⊤) ∧
      (∀ n ω t, t < ⊤ → ∃ j, t < τ n j ω) ∧
      (∀ i n j ω t,
        ‖X i (min (τ n (j+1) ω) t) ω-X i (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n) ∧
      (∀ i n j t, eLpNorm (fun ω =>
        X i (min (τ n (j+1) ω) t) ω-X i (min (τ n j ω) t) ω) ∞ P
          ≤ ENNReal.ofReal ((1/2:ℝ)^n)) := by
  let V := fun t ω i => X i t ω
  let τ := fun n => vectorOscillationPartition V c ((1/2:ℝ)^n)
  have hv : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t := by
    intro ω t ht
    exact continuousAt_pi.mpr (fun i => hX i ω t ht)
  have hp n := constructed_finite_vector_oscillation_partition F hF V hm hv c hc hct hcc
    ((1/2:ℝ)^n) (pow_pos (by norm_num) n)
  have hb i n j ω t :
      ‖X i (min (τ n (j+1) ω) t) ω-X i (min (τ n j ω) t) ω‖ ≤ (1/2:ℝ)^n := by
    exact (norm_le_pi_norm (V (min (τ n (j+1) ω) t) ω-
      V (min (τ n j ω) t) ω) i).trans ((hp n).2.2.2.2.2 j ω t)
  refine ⟨τ,fun n => (hp n).1,fun n => (hp n).2.1,
    fun n => (hp n).2.2.1,fun n => (hp n).2.2.2.1,
    fun n => (hp n).2.2.2.2.1,hb,?_⟩
  intro i n j t
  have hs k := (open_continuous_adapted_stopped_regular F hF (X i) (hm i) (hX i)
    c hc hct hcc (τ n k) ((hp n).2.1 k) ((hp n).2.2.2.1 k)).1 t
  have hmeas : Measurable (fun ω =>
      X i (min (τ n (j+1) ω) t) ω-X i (min (τ n j ω) t) ω) :=
    ((hs (j+1)).sub (hs j)).mono (hle t) le_rfl
  simpa using (eLpNorm_le_of_ae_bound (p := ∞) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => hb i n j ω t)))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.common_oscillation_partition
