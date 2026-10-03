import Chapter7ShiftedBlockMoments

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma brownian_block_adapted {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (B : BrownianSystem P d)
    (u v : Fin d → ℝ) (s h : ℝ) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    StronglyMeasurable[B.F (realTimeClamp (s+h))] (fun w => ∫ r in 0..h,
      (∑ j,u j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))*
      (∑ j,v j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))) := by
  let F := B.F (realTimeClamp (s+h))
  let c := fun r : ℝ => s+min h (max 0 r)
  have hc : Continuous c := continuous_const.add (continuous_const.min (continuous_const.max continuous_id))
  have hc0 r : 0 ≤ c r := add_nonneg hs (le_min hh (le_max_left _ _))
  have hct r : c r ≤ s+h := add_le_add le_rfl (min_le_left _ _)
  let X := fun (a : Fin d → ℝ) r w => ∑ j,a j*(B.W j (realTimeClamp (c r)) w-B.W j (realTimeClamp s) w)
  have hcont a w : Continuous (fun r => X a r w) := by
    apply continuous_finset_sum
    intro j _
    apply continuous_const.mul
    apply Continuous.sub _ continuous_const
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (((B.martingale j).path P B.F w _ (changed_time_finite _ (hc0 r))).comp
      real_time_clamp_continuous.continuousAt).comp hc.continuousAt
  have hmeas a r : Measurable[F] (X a r) := by
    letI : MeasurableSpace Ω := F
    apply Finset.measurable_sum
    intro j _
    apply measurable_const.mul
    exact (((B.martingale j).adapted P B.F _ (changed_time_finite _ (hc0 r))).mono
      (B.mono (real_time_clamp_mono (hct r))) le_rfl).sub
      (((B.martingale j).adapted P B.F _ (changed_time_finite _ hs)).mono
        (B.mono (real_time_clamp_mono (le_add_of_nonneg_right hh))) le_rfl)
  letI : MeasurableSpace Ω := F
  have hm a : Measurable (fun z : Ω × ℝ => X a z.2 z.1) := by
    have hj : Measurable (Function.uncurry (X a)) :=
      measurable_uncurry_of_continuous_of_measurable (hcont a) (hmeas a)
    simpa only [Function.comp_def,Function.uncurry_def,Prod.swap] using hj.comp measurable_swap
  have hi := ((hm u).mul (hm v)).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) h))
  have he w : (∫ r in Ioc 0 h,X u r w*X v r w)=∫ r in 0..h,
      (∑ j,u j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w))*
      (∑ j,v j*(B.W j (realTimeClamp (s+r)) w-B.W j (realTimeClamp s) w)) := by
    rw [intervalIntegral.integral_of_le hh]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [X,c,max_eq_right hr.1.le,min_eq_right hr.2]
  simpa only [Pi.mul_apply,he] using hi

end Asakura.Chapter7
