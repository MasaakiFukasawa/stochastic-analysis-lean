import Chapter7InverseClock
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

open Set Filter Topology
open scoped NNReal Topology
namespace Asakura.Chapter7
set_option maxHeartbeats 800000

/-- On a compact interval the clock is a continuous surjection. Its quotient
property supplies the continuity across flat portions of the clock. -/
theorem clock_path_continuousOn {E : Type*} [TopologicalSpace E]
    (A : ℝ≥0 → ℝ≥0) (hA : Continuous A) (hm : Monotone A)
    (hu : ∀ s,∃ t,s ≤ A t) (hzero : A 0 = 0)
    (X : ℝ≥0 → E) (hX : Continuous X)
    (hflat : ∀ s t,A s = A t → X s = X t) (R : ℝ≥0) :
    ContinuousOn (fun s => X (firstClockTime A s)) (Icc 0 (A R)) := by
  let f : Icc (0 : ℝ≥0) R → Icc (0 : ℝ≥0) (A R) :=
    fun t => ⟨A t,bot_le,hm t.property.2⟩
  have hf : Continuous f := (hA.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective f := by
    intro s
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ R from bot_le)
      hA.continuousOn (show (s : ℝ≥0) ∈ Icc (A 0) (A R) by simpa [hzero] using s.property)
    exact ⟨⟨t,ht⟩,Subtype.ext he⟩
  have hq := IsQuotientMap.of_surjective_continuous hs hf
  rw [continuousOn_iff_continuous_domRestrict]
  apply hq.continuous_iff.mpr
  have he : (fun s : Icc (0 : ℝ≥0) (A R) => X (firstClockTime A s)) ∘ f =
      fun t : Icc (0 : ℝ≥0) R => X t := by
    funext t
    exact path_recovered_from_clock A hA hm hu hzero X hflat t
  change Continuous ((fun s : Icc (0 : ℝ≥0) (A R) => X (firstClockTime A s)) ∘ f)
  rw [he]
  exact hX.comp continuous_subtype_val

/-- The time-changed path is continuous on the entire half-line, without
requiring the generalized inverse clock itself to be continuous. -/
theorem clock_path_continuous {E : Type*} [TopologicalSpace E]
    (A : ℝ≥0 → ℝ≥0) (hA : Continuous A) (hm : Monotone A)
    (hu : ∀ s,∃ t,s ≤ A t) (hzero : A 0 = 0)
    (X : ℝ≥0 → E) (hX : Continuous X)
    (hflat : ∀ s t,A s = A t → X s = X t) :
    Continuous (fun s => X (firstClockTime A s)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨R,hR⟩ := hu (s+1)
  have hs : s < A R := lt_of_lt_of_le (lt_add_one s) hR
  apply (clock_path_continuousOn A hA hm hu hzero X hX hflat R).continuousAt
  have he : Icc (0 : ℝ≥0) (A R) = Iic (A R) := by ext t; simp
  rw [he]
  exact Iic_mem_nhds hs

end Asakura.Chapter7
