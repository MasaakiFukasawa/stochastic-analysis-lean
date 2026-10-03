import FullAuditStoppedMeanExercise
import FullAuditClosedHitting

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A continuous zero-initial martingale cannot hit a fixed nonzero level
 by a deterministic terminal time with probability one. The first hitting
 time is constructed, is a stopping time, and attains the level whenever
 it is reached; optional sampling supplies the contradiction. -/
theorem nonzero_level_not_hit_by_terminal {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hi : ∀ t, Integrable (X t) P) (hc : ∀ ω, Continuous (fun t => X t ω))
    (hM : ∀ s t, s ≤ t → P[X t | F s] =ᵐ[P] X s) (hz : X ⊥ =ᵐ[P] 0)
    (c : ℝ) (hc0 : c ≠ 0) : 0 < P {ω | ∀ t, X t ω ≠ c} := by
  by_contra hn
  have hzero : P {ω | ∀ t, X t ω ≠ c} = 0 := le_antisymm (not_lt.mp hn) zero_le
  have hhit : ∀ᵐ ω ∂P, ∃ t, X t ω = c := by
    rw [ae_iff]
    simpa only [not_exists] using hzero
  let τ : Ω → ClosedTime T := fun ω => sInf {t | X t ω ∈ ({c}:Set ℝ)}
  have hτ := closed_hitting_stopping_compact F hF X hm hc ({c}:Set ℝ) isClosed_singleton
  have hval : (fun ω => X (τ ω) ω) =ᵐ[P] (fun _ => c) := by
    filter_upwards [hhit] with ω hω
    have hne : {t | X t ω ∈ ({c}:Set ℝ)}.Nonempty := by
      obtain ⟨t,ht⟩ := hω
      exact ⟨t,ht⟩
    have hs := IsClosed.sInf_mem hne (isClosed_singleton.preimage (hc ω))
    exact hs
  have hmean := (zero_stopped_mean_exercise P (Fact.out : 0 ≤ T) F hF hle X hm hi
    (fun ω t => (hc ω).continuousAt.continuousWithinAt) hz).mp hM τ hτ
  have he := integral_congr_ae hval
  rw [integral_const,probReal_univ,one_smul,hmean.2] at he
  exact hc0 he.symm

end Asakura.FullAudit
