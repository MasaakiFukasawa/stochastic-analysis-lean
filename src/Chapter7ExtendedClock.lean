import Chapter7InverseExerciseWritten

open Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.Chapter2Written
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The original half-open clock, with its divergent endpoint recorded as
an extended real value. No real value at the terminal time is assumed. -/
noncomputable def extendedClock {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (t : ClosedTime T) : EReal :=
  if t < ⊤ then (C t : EReal) else ⊤

lemma extended_clock_finite {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (t : ClosedTime T) (ht : t < ⊤) :
    extendedClock C t = (C t : EReal) := if_pos ht

lemma extended_clock_top {T : EReal} [Fact (0 ≤ T)] (C : ClosedTime T → ℝ) :
    extendedClock C ⊤ = ⊤ := if_neg (lt_irrefl _)

lemma extended_clock_monotone {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (hm : MonotoneOn C (Iio ⊤)) : Monotone (extendedClock C) := by
  intro s t hst
  by_cases ht : t < ⊤
  · rw [extended_clock_finite C t ht,extended_clock_finite C s (hst.trans_lt ht)]
    exact_mod_cast hm (hst.trans_lt ht) ht hst
  · simp only [extendedClock,if_neg ht,le_top]

lemma extended_clock_continuous {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (hc : ∀ t,t < ⊤ → ContinuousAt C t) :
    ContinuousOn (extendedClock C) (Iio ⊤) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  apply (continuous_coe_real_ereal.continuousAt.comp (hc t ht)).congr_of_eventuallyEq
  exact (gt_mem_nhds ht).mono (fun s hs => extended_clock_finite C s hs)

lemma extended_clock_right_continuous {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (hc : ∀ t,t < ⊤ → ContinuousAt C t) :
    ∀ t,ContinuousWithinAt (extendedClock C) (Ici t) t := by
  intro t
  by_cases ht : t < ⊤
  · exact ((extended_clock_continuous C hc).continuousAt (Iio_mem_nhds ht)).continuousWithinAt
  · have he : t = ⊤ := eq_top_iff.mpr (le_of_not_gt ht)
    subst t
    simp only [Ici_top]
    exact continuousWithinAt_singleton

lemma extended_clock_endpoint_supremum {T : EReal} [Fact (0 ≤ T)]
    (C : ClosedTime T → ℝ) (hu : ∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t) :
    extendedClock C ⊤ = sSup (extendedClock C '' Iio ⊤) := by
  rw [extended_clock_top]
  apply Eq.symm
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro r
  obtain ⟨t,ht,hr⟩ := hu r
  have hh : (r:EReal) < extendedClock C t := by
    rw [extended_clock_finite C t ht]
    exact_mod_cast hr
  exact hh.trans_le (le_sSup (mem_image_of_mem _ ht))

end Asakura.Chapter7
