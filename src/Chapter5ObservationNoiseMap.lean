import Chapter5LinearGeneratorPullback
import Chapter5StoppedCovarianceGram
import Mathlib.Analysis.Normed.Operator.Prod

open Set
open scoped BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 1800000

noncomputable def observationNoiseMap {d k : ℕ} (index : Fin k → Fin d)
    (active : Fin k → Prop) [DecidablePred active] : (Fin d → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ContinuousLinearMap.pi (fun i => if active i then ContinuousLinearMap.proj (index i) else 0)

theorem observationNoiseMap_basis {d k : ℕ} (index : Fin k → Fin d)
    (active : Fin k → Prop) [DecidablePred active] (l : Fin d) (i : Fin k) :
    observationNoiseMap index active (Pi.single l 1) i=
      if active i ∧ index i=l then (1:ℝ) else 0 := by
  classical
  by_cases ha : active i <;> by_cases hi : index i=l <;>
    simp [observationNoiseMap,ha,hi,Pi.single_apply,eq_comm]

/-- On the open part of the current interval, all past coordinates are
inactive and all current coordinates retain their Brownian noise. -/
theorem observation_noise_before_endpoint {d k : ℕ} (index : Fin k → Fin d)
    (active : Fin k → Prop) [DecidablePred active] (τ : Fin k → ℝ)
    (a b r : ℝ) (har : a≤r) (hrb : r<b)
    (hpast : ∀ i,¬active i → τ i≤a) (hcurrent : ∀ i,active i → τ i=b)
    (l : Fin d) (i : Fin k) :
    (if r<τ i ∧ index i=l then (1:ℝ) else 0)=observationNoiseMap index active (Pi.single l 1) i := by
  rw [observationNoiseMap_basis]
  by_cases ha : active i
  · rw [hcurrent i ha]
    simp [ha,hrb]
  · have hi : ¬r<τ i := not_lt_of_ge ((hpast i ha).trans har)
    simp [ha,hi]

/-- At the chosen endpoint every stopped coordinate has zero open-cutoff
noise density, so the generator cancels there as well. -/
theorem observation_noise_at_endpoint {d k : ℕ} (index : Fin k → Fin d)
    (τ : Fin k → ℝ) (b : ℝ) (hτ : ∀ i,τ i≤b) (l : Fin d) (i : Fin k) :
    (if b<τ i ∧ index i=l then (1:ℝ) else 0)=0 := by
  simp [not_lt_of_ge (hτ i)]

end Asakura.Chapter5
