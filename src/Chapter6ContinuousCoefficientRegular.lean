import Chapter6BrownianContinuousCoefficient
import Chapter4FinitePathLift

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Stop a continuous state-dependent coefficient at the finite horizon.
The extension is continuous even at infinity and retains adaptedness. -/
theorem stopped_continuous_coefficient_regular {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (b : ℝ × (Fin d → ℝ) → Fin d → ℝ) (hb : Continuous b)
    (R : ℝ) (hR : 0≤R) :
    let H := stoppedBrownianCoefficient P B b R hR
    (∀ j t,Measurable[B.F t] (H j t)) ∧
    (∀ j w,Continuous (fun t => H j t w)) ∧
    (∀ j w r,r∈Icc 0 R → H j (realTimeClamp r) w=b (r,fun i => B.W i (realTimeClamp r) w) j) := by
  let H := stoppedBrownianCoefficient P B b R hR
  have hRt : (realTimeClamp R : HalfClosedTime)<⊤ := changed_time_finite R hR
  have hWa i t : Measurable[B.F t] (fun w => B.W i (min (realTimeClamp R) t) w) :=
    ((B.martingale i).adapted P B.F _ ((min_le_left _ _).trans_lt hRt)).mono (B.mono (min_le_right _ _)) le_rfl
  have hWc i w : Continuous (fun t => B.W i (min (realTimeClamp R) t) w) :=
    open_path_stopped_continuous (B.W i) ((B.martingale i).path P B.F) R hR (EReal.coe_lt_top _) w
  refine ⟨?_,?_,?_⟩
  · intro j t
    letI : MeasurableSpace Ω := B.F t
    exact (measurable_pi_apply j).comp (hb.measurable.comp (measurable_const.prodMk (measurable_pi_iff.mpr (fun i => hWa i t))))
  · intro j w
    exact (continuous_apply j).comp (hb.comp
      ((continuous_subtype_val.comp (finite_prefix_time_continuous R hR)).prodMk (continuous_pi (fun i => hWc i w))))
  · intro j w r hr
    dsimp [H,stoppedBrownianCoefficient]
    rw [finite_prefix_time_of_real R r hR hr (show (R:EReal)≤⊤ from le_top),
      min_eq_right (real_time_clamp_mono hr.2)]

end Asakura.Chapter6
