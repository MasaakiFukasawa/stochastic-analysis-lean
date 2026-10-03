import Chapter7BrownianStoppedMean

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000

lemma brownian_clock_at_finite
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSystem P 1)
    (t : HalfClosedTime) (ht : t < ⊤) (w) :
    B.C 0 0 t w = (halfTimeReal t : ℝ) := by
  obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t ht
  rw [changed_time_real r hr]
  exact B.diagonal_clock 0 w r hr

/-- Bounds needed for both stopped-moment identities follow directly from
no overshoot and the deterministic time cap. -/
theorem brownian_exit_path_bounds
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (x R c : ℝ) (hc : 0 ≤ c)
    (τ : Ω → HalfClosedTime) (hτc : ∀ w,τ w ≤ realTimeClamp c)
    (hb : ∀ᵐ w ∂P,∀ t,x+B.W 0 (min (τ w) t) w ∈ Icc 0 R) :
    (∀ᵐ w ∂P,∀ t,|B.W 0 (min (τ w) t) w| ≤ |R|+|x|) ∧
    (∀ᵐ w ∂P,∀ t,
      |B.W 0 (min (τ w) t) w * B.W 0 (min (τ w) t) w -
        B.C 0 0 (min (τ w) t) w| ≤ (|R|+|x|)^2+c) := by
  have hbound : ∀ᵐ w ∂P,∀ t,|B.W 0 (min (τ w) t) w| ≤ |R|+|x| := by
    filter_upwards [hb] with w hw
    intro t
    have hz := hw t
    have hab : |x+B.W 0 (min (τ w) t) w| ≤ |R| := by
      rw [abs_of_nonneg hz.1]
      exact hz.2.trans (le_abs_self R)
    calc
      |B.W 0 (min (τ w) t) w| = |(x+B.W 0 (min (τ w) t) w)-x| := by congr 1; ring
      _ ≤ |x+B.W 0 (min (τ w) t) w|+|x| := abs_sub _ _
      _ ≤ |R|+|x| := by linarith
  refine ⟨hbound,?_⟩
  filter_upwards [hbound] with w hw
  intro t
  have hfin : min (τ w) t < ⊤ := lt_of_le_of_lt ((min_le_left _ _).trans (hτc w)) (changed_time_finite c hc)
  obtain ⟨r,hr,_,he⟩ := finite_closed_time_real (min (τ w) t) hfin
  have hrc : r ≤ c := by
    have h := (min_le_left (τ w) t).trans (hτc w)
    rw [← he] at h
    exact (changed_time_le_iff r hr _ (changed_time_finite c hc)).mp h |>.trans_eq (changed_time_real c hc)
  have hclock : B.C 0 0 (min (τ w) t) w = r := by rw [← he]; exact B.diagonal_clock 0 w r hr
  calc
    |B.W 0 (min (τ w) t) w * B.W 0 (min (τ w) t) w - B.C 0 0 (min (τ w) t) w|
      ≤ |B.W 0 (min (τ w) t) w * B.W 0 (min (τ w) t) w| + |B.C 0 0 (min (τ w) t) w| := abs_sub _ _
    _ ≤ (|R|+|x|)^2+c := by
      rw [abs_mul,hclock,abs_of_nonneg hr]
      nlinarith [hw t,abs_nonneg (B.W 0 (min (τ w) t) w),abs_nonneg R,abs_nonneg x]

end Asakura.Chapter7
