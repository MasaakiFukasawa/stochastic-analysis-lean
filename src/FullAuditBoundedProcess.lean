import FullAuditQuadraticVariation

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- Actual continuous bounded martingale versions, before identifying
 indistinguishable paths. All equalities of the chosen variations below
 are consequently stated outside a common null set. -/
noncomputable def boundedMProcess {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) : Submodule ℝ (ClosedTime T → Ω → ℝ) where
  carrier := {X | ContinuousM2Witness P F X ∧ ∀ t, MemLp (X t) ∞ P}
  zero_mem' := ⟨ContinuousM2Witness.zero P F,fun _ => MemLp.zero⟩
  add_mem' := by
    rintro X Y ⟨hX,hXt⟩ ⟨hY,hYt⟩
    exact ⟨hX.add P F hY,fun t => (hXt t).add (hYt t)⟩
  smul_mem' := by
    rintro c X ⟨hX,hXt⟩
    exact ⟨hX.smul P F c,fun t => (hXt t).const_smul c⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)

include hF hle hnull

/-- Existence is the preceding written proof, not an assumed QV operator. -/
theorem bounded_process_has_qv (X : boundedMProcess P F) :
    ∃ A : ClosedTime T → Ω → ℝ, (∀ t, Measurable[F t] (A t)) ∧
      (∀ ω, Continuous (fun t => A t ω)) ∧ (∀ ω, Monotone (fun t => A t ω)) ∧
      ContinuousM2Witness P F (fun t ω => X.val t ω^2-A t ω) := by
  obtain ⟨A,hm,hc,ho,hY,-⟩ := quadratic_variation_exists_unique_written P F hF hle hnull X.val
    X.property.1.adapted X.property.2 X.property.1.path X.property.1.martingale X.property.1.initial
  exact ⟨A,hm,hc,ho,hY⟩

noncomputable def boundedQV (X : boundedMProcess P F) : ClosedTime T → Ω → ℝ :=
  Classical.choose (bounded_process_has_qv P F hF hle hnull X)

theorem boundedQV_properties (X : boundedMProcess P F) :
    (∀ t, Measurable[F t] (boundedQV P F hF hle hnull X t)) ∧
    (∀ ω, Continuous (fun t => boundedQV P F hF hle hnull X t ω)) ∧
    (∀ ω, Monotone (fun t => boundedQV P F hF hle hnull X t ω)) ∧
    ContinuousM2Witness P F (fun t ω => X.val t ω^2-boundedQV P F hF hle hnull X t ω) :=
  Classical.choose_spec (bounded_process_has_qv P F hF hle hnull X)

noncomputable def boundedCov (X Y : boundedMProcess P F) : ClosedTime T → Ω → ℝ :=
  fun t ω => (boundedQV P F hF hle hnull (X+Y) t ω-boundedQV P F hF hle hnull (X-Y) t ω)/4

end Asakura.FullAudit
