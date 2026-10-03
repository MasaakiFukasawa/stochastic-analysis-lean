import Chapter7ClockInverseStopping
import Chapter7RightClockStopping
import Chapter7ClockHalfTime

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The original bracket at a fixed original time is a stopping time for
the right-continuous changed filtration. Strict comparison events and the
future intersection are both proved explicitly. -/
theorem forward_clock_stopping
    {Ω : Type*} {m : MeasurableSpace Ω} {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (C : ClosedTime T → Ω → ℝ)
    (hCa : ∀ t,t < ⊤ → Measurable[F t] (C t))
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (hCc : ∀ w t,t < ⊤ → ContinuousAt (fun s => C s w) t)
    (hC0 : ∀ w,C ⊥ w = 0) (hCu : ∀ w r,∃ t,t < ⊤ ∧ r < C t w)
    (a : ClosedTime T) (ha : a < ⊤) :
    let τ := fun r w => inverseRealClock (fun t => C t w) r
    let hτ := real_clock_inverse_stopping hT F C hCa hCm hCc hC0 hCu
    let G := fun s : ℝ≥0 => ⨅ r : Ioi (s:ℝ),writtenStoppedSpace m F (τ r.val) (hτ r.val)
    ∀ t : HalfClosedTime,MeasurableSet[halfClosedFiltration m G t]
      {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t} := by
  let τ := fun r w => inverseRealClock (fun t => C t w) r
  let hτ := real_clock_inverse_stopping hT F C hCa hCm hCc hC0 hCu
  let H := fun r => writtenStoppedSpace m F (τ r) (hτ r)
  let G := fun s : ℝ≥0 => ⨅ r : Ioi (s:ℝ),H r.val
  have hp w := real_clock_inverse_properties hT (fun t => C t w) (hCm w) (hCc w) (hC0 w) (hCu w)
  have hCn w : 0 ≤ C a w := by simpa only [hC0 w] using hCm w hT ha bot_le
  have hHm : Monotone H := fun r s hrs => written_stoppedSpace_mono m F
    (τ r) (τ s) (hτ r) (hτ s) (fun w => (hp w).1 hrs)
  have hstrict r : MeasurableSet[H r] {w | C a w < r} := by
    by_cases hr : 0 < r
    · have hconst t : MeasurableSet[F t] {w : Ω | a ≤ t} := by
        by_cases ht : a ≤ t <;> simp [ht]
      have hh := (written_extended_comparison m (ClosedTime T) F hF hle
        (fun _ => a) (τ r) hconst (hτ r)).1
      have hinc : writtenStoppedSpace m F (fun _ => a) hconst ⊓ H r ≤ H r := inf_le_right
      have hh' : MeasurableSet[H r] {w | a < τ r w} := hinc _ hh
      have he : {w | C a w < r} = {w | a < τ r w} := by
        ext w
        have h := ((hp w).2.2.2.2 r a ha).not
        simpa only [mem_setOf_eq,τ,not_le,max_eq_right hr.le] using h.symm
      rwa [he]
    · have he : {w | C a w < r} = ∅ := by
        ext w
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        exact not_lt_of_ge ((le_of_not_gt hr).trans (hCn w))
      rw [he]
      exact @MeasurableSet.empty Ω (H r)
  change ∀ t : HalfClosedTime,MeasurableSet[halfClosedFiltration m G t]
    {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t}
  intro t
  by_cases ht : t < ⊤
  · have hbase := right_filtration_clock_stopping H hHm (C a) hstrict (halfTimeReal t)
    have he : {w | realTimeClamp (T := (⊤:EReal)) (C a w) ≤ t} = {w | C a w ≤ (halfTimeReal t : ℝ)} := by
      ext w
      exact changed_time_le_iff (C a w) (hCn w) t ht
    rw [he]
    have hinc : G (halfTimeReal t) ≤ halfClosedFiltration m G t := by simp only [halfClosedFiltration,if_pos ht,le_refl]
    exact hinc _ hbase
  · have he : t = ⊤ := eq_top_iff.mpr (le_of_not_gt ht)
    subst t
    simp only [le_top,Set.setOf_true]
    exact MeasurableSet.univ

end Asakura.Chapter7
