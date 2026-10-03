import Chapter7BrownianProjectionRegular
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- The increment after s, set to zero before s, is continuous and adapted. -/
lemma brownian_future_projection {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u : Fin d → ℝ) (s : ℝ) (hs : 0≤s) :
    let X := fun r w => ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) w-
      B.W j (realTimeClamp (min s (max 0 r))) w)
    (∀ w,Continuous (fun r => X r w)) ∧
    Measurable (fun z : Ω × ℝ => X z.2 z.1) ∧
    (∀ r,0≤r → Measurable[B.F (realTimeClamp r)] (X r)) := by
  let X := fun r w => ∑ j,u j*(B.W j (realTimeClamp (max 0 r)) w-
      B.W j (realTimeClamp (min s (max 0 r))) w)
  have hc w : Continuous (fun r => X r w) := by
    apply continuous_finsetSum
    intro j _
    apply continuous_const.mul
    apply Continuous.sub
    · apply continuous_iff_continuousAt.mpr
      intro r
      exact (((B.martingale j).path P B.F w _ (changed_time_finite _ (le_max_left _ _))).comp
        real_time_clamp_continuous.continuousAt).comp (continuous_const.max continuous_id).continuousAt
    · apply continuous_iff_continuousAt.mpr
      intro r
      exact ((((B.martingale j).path P B.F w _ (changed_time_finite _ (le_min hs (le_max_left _ _)))).comp
        real_time_clamp_continuous.continuousAt).comp
        (continuous_const.min continuous_id).continuousAt).comp
        (continuous_const.max continuous_id).continuousAt
  have ha r (hr : 0≤r) : Measurable[B.F (realTimeClamp r)] (X r) := by
    letI : MeasurableSpace Ω := B.F (realTimeClamp r)
    dsimp only [X]
    simp only [max_eq_right hr]
    apply Finset.measurable_sum
    intro j _
    exact measurable_const.mul (((B.martingale j).adapted P B.F _ (changed_time_finite _ hr)).sub
      (((B.martingale j).adapted P B.F _ (changed_time_finite _ (le_min hs hr))).mono
        (B.mono (real_time_clamp_mono (min_le_right _ _))) le_rfl))
  have hm r : Measurable[m] (X r) := by
    have he : X r=X (max 0 r) := by simp only [X,max_eq_right (le_max_left 0 r)]
    rw [he]
    exact (ha _ (le_max_left _ _)).mono (B.le _) le_rfl
  have hj : Measurable (Function.uncurry X) := measurable_uncurry_of_continuous_of_measurable hc hm
  refine ⟨hc,?_,ha⟩
  simpa only [Function.comp_def,Function.uncurry_def,Prod.swap] using hj.comp measurable_swap

end Asakura.Chapter7
