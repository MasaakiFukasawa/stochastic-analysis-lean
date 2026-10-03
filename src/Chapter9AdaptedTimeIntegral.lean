import Chapter9ReverseTestIncrement

open MeasureTheory Set
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Measurability of a past time integral follows from path continuity and
 adapted sections; no extra choice of jointly measurable representatives. -/
theorem measurable_past_integral {Ω : Type*} [m : MeasurableSpace Ω]
    (a : ℝ → Ω → ℝ) (s : ℝ) (hs : 0≤s)
    (ha : ∀ r∈Icc 0 s,Measurable (a r))
    (hc : ∀ w,ContinuousOn (fun r => a r w) (Icc 0 s)) :
    Measurable (fun w => ∫ r in 0..s,a r w) := by
  let c := fun r : ℝ => max 0 (min r s)
  have hcm r : c r∈Icc 0 s := ⟨le_max_left _ _,max_le hs (min_le_right _ _)⟩
  have hcc : Continuous c := by fun_prop
  have hm : Measurable (fun z : ℝ × Ω => a (c z.1) z.2) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun w => (hc w).comp_continuous hcc hcm) (fun r => ha _ (hcm r))
  have hi : Measurable (fun w => ∫ r,a (c r) w ∂volume.restrict (Ioc 0 s)) :=
    (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  convert hi using 1
  funext w
  rw [intervalIntegral.integral_of_le hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr
  dsimp only [c]
  rw [min_eq_left hr.2,max_eq_right hr.1.le]

theorem integrable_bounded_time_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (a : ℝ → Ω → ℝ)
    (hm : Measurable (fun z : ℝ × Ω => a z.1 z.2))
    (s : ℝ) (hs : 0≤s) (C : ℝ) (hb : ∀ r∈Ioc 0 s,∀ w,‖a r w‖≤C) :
    Integrable (fun w => ∫ r in 0..s,a r w) P := by
  have hi : Integrable (fun z : Ω × ℝ => a z.2 z.1) (P.prod (volume.restrict (Ioc 0 s))) :=
    Integrable.of_bound (hm.comp measurable_swap).aestronglyMeasurable C
      (measurable_product_bound P _ _ (hm.comp measurable_swap) C
        ((ae_restrict_mem measurableSet_Ioc).mono (fun r hr => ae_of_all _ (hb r hr))))
  simpa only [intervalIntegral.integral_of_le hs] using hi.integral_prod_left
end Asakura.Chapter9
