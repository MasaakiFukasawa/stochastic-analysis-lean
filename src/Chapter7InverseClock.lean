import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.NNReal.Lemmas

open Set Filter
open scoped NNReal Topology
namespace Asakura.Chapter7

/-- The first time the clock reaches a level. -/
noncomputable def firstClockTime (A : ℝ≥0 → ℝ≥0) (s : ℝ≥0) : ℝ≥0 :=
  sInf {t | s ≤ A t}

lemma firstClockTime_le (A : ℝ≥0 → ℝ≥0) (s t : ℝ≥0) (h : s ≤ A t) :
    firstClockTime A s ≤ t := csInf_le (OrderBot.bddBelow _) h

lemma level_le_at_firstClockTime (A : ℝ≥0 → ℝ≥0) (hA : Continuous A)
    (hu : ∀ s, ∃ t, s ≤ A t) (s : ℝ≥0) :
    s ≤ A (firstClockTime A s) := by
  exact (isClosed_le continuous_const hA).csInf_mem (hu s) (OrderBot.bddBelow _)

/-- The stopping-time event equality used in both time-change constructions. -/
theorem firstClockTime_le_iff (A : ℝ≥0 → ℝ≥0) (hA : Continuous A)
    (hm : Monotone A) (hu : ∀ s, ∃ t, s ≤ A t) (s t : ℝ≥0) :
    firstClockTime A s ≤ t ↔ s ≤ A t := by
  exact ⟨fun h => (level_le_at_firstClockTime A hA hu s).trans (hm h),
    firstClockTime_le A s t⟩

lemma firstClockTime_monotone (A : ℝ≥0 → ℝ≥0) (hA : Continuous A)
    (hm : Monotone A) (hu : ∀ s, ∃ t, s ≤ A t) : Monotone (firstClockTime A) := by
  intro s r hsr
  exact (firstClockTime_le_iff A hA hm hu s _).mpr
    (hsr.trans (level_le_at_firstClockTime A hA hu r))

/-- Continuity prevents overshooting a level, even when A has flat pieces. -/
theorem clock_at_firstClockTime (A : ℝ≥0 → ℝ≥0) (hA : Continuous A)
    (hm : Monotone A) (hu : ∀ s, ∃ t, s ≤ A t) (hzero : A 0 = 0)
    (s : ℝ≥0) : A (firstClockTime A s) = s := by
  obtain ⟨t,ht⟩ := hu s
  have hs : s ∈ Icc (A 0) (A t) := by simpa [hzero] using And.intro (show 0 ≤ s from bot_le) ht
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (show 0 ≤ t from bot_le) hA.continuousOn hs
  apply le_antisymm _ (level_le_at_firstClockTime A hA hu s)
  calc
    A (firstClockTime A s) ≤ A r := hm (firstClockTime_le A s r he.ge)
    _ = s := he

/-- A path constant on clock level sets is recovered exactly after time change. -/
theorem path_recovered_from_clock {E : Type*} (A : ℝ≥0 → ℝ≥0) (hA : Continuous A)
    (hm : Monotone A) (hu : ∀ s, ∃ t, s ≤ A t) (hzero : A 0 = 0)
    (X : ℝ≥0 → E) (hflat : ∀ s t, A s = A t → X s = X t) (t : ℝ≥0) :
    X (firstClockTime A (A t)) = X t :=
  hflat _ _ (clock_at_firstClockTime A hA hm hu hzero (A t))

end Asakura.Chapter7
