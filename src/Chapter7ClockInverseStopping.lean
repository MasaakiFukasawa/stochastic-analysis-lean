import Chapter7RealClockInverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter7
open Asakura.Chapter2Written
set_option maxHeartbeats 1600000

/-- The inverse defined by an infimum is an actual stopping time, from the
adapted bracket's superlevel events, on a finite or infinite original horizon. -/
theorem real_clock_inverse_stopping
    {Ω : Type*} {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω)
    (C : ClosedTime T → Ω → ℝ)
    (hCa : ∀ t,t < ⊤ → Measurable[F t] (C t))
    (hCm : ∀ w,MonotoneOn (fun t => C t w) (Iio ⊤))
    (hCc : ∀ w t,t < ⊤ → ContinuousAt (fun s => C s w) t)
    (hC0 : ∀ w,C ⊥ w = 0) (hCu : ∀ w r,∃ t,t < ⊤ ∧ r < C t w)
    (r : ℝ) (t : ClosedTime T) :
    MeasurableSet[F t] {w | inverseRealClock (fun t => C t w) r ≤ t} := by
  by_cases ht : t < ⊤
  · have he : {w | inverseRealClock (fun t => C t w) r ≤ t} = {w | max 0 r ≤ C t w} := by
      ext w
      exact (real_clock_inverse_properties hT (fun t => C t w) (hCm w) (hCc w) (hC0 w) (hCu w)).2.2.2.2 r t ht
    rw [he]
    exact measurableSet_le measurable_const (hCa t ht)
  · have he : t = ⊤ := eq_top_iff.mpr (le_of_not_gt ht)
    subst t
    simp only [le_top,Set.setOf_true]
    exact MeasurableSet.univ

/-- Clock and path stopping identities, with no inverse continuity assumed. -/
theorem real_clock_stopping_identities
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (C : ClosedTime T → ℝ) (hm : MonotoneOn C (Iio ⊤))
    (hc : ∀ t,t < ⊤ → ContinuousAt C t) (hz : C ⊥ = 0)
    (hu : ∀ r : ℝ,∃ t,t < ⊤ ∧ r < C t)
    (X : ClosedTime T → ℝ)
    (hflat : ∀ a b,a < ⊤ → b < ⊤ → C a = C b → X a = X b)
    (a : ClosedTime T) (ha : a < ⊤) (r : ℝ) :
    C (min a (inverseRealClock C r)) = C (inverseRealClock C (min (C a) r)) ∧
    X (min a (inverseRealClock C r)) = X (inverseRealClock C (min (C a) r)) := by
  have hp := real_clock_inverse_properties hT C hm hc hz hu
  have hn : 0 ≤ C a := by simpa only [hz] using hm (show (⊥ : ClosedTime T) < ⊤ from hT) ha bot_le
  have hmin : C (min a (inverseRealClock C r)) = min (C a) (C (inverseRealClock C r)) := by
    rcases le_total a (inverseRealClock C r) with h | h
    · rw [min_eq_left h,min_eq_left (hm ha (hp.2.2.1 r) h)]
    · rw [min_eq_right h,min_eq_right (hm (hp.2.2.1 r) ha h)]
  have he : C (min a (inverseRealClock C r)) = C (inverseRealClock C (min (C a) r)) := by
    rw [hmin,hp.2.2.2.1,hp.2.2.2.1,max_min_distrib_left,max_eq_right hn,min_comm (C a)]
  exact ⟨he,hflat _ _ ((min_le_left _ _).trans_lt ha) (hp.2.2.1 _) he⟩

end Asakura.Chapter7
