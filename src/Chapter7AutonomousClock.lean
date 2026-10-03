import Chapter7TimeChangeSDEWritten
import Chapter5ProgressivePrimitive
import Chapter5ProgressiveDriftVariation
import Chapter7DivergentPositivePrimitive

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the autonomous inverse-speed clock as an actual time integral.
Its adaptedness, regularity, initial value, derivative and divergence are
all outputs, rather than assumptions of the time-change application. -/
theorem autonomous_clock_constructed
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (σ : ℝ → ℝ) (hc : Continuous σ) (hn : ∀ x,σ x ≠ 0)
    (hdiv : ∀ w,(∫⁻ r in Ici (0:ℝ),ENNReal.ofReal
      (1/(σ (B.W 0 (realTimeClamp r) w))^2)) = ∞) :
    ∃ A : HalfClosedTime → Ω → ℝ,
      (∀ t,t < ⊤ → Measurable[B.F t] (A t)) ∧
      (∀ w t,t < ⊤ → ContinuousAt (fun s => A s w) t) ∧
      (∀ w,A ⊥ w = 0) ∧
      (∀ w R,∃ t,t < ⊤ ∧ R < A t w) ∧
      (∀ w r,0 < r → HasDerivAt (fun s => A (realTimeClamp s) w)
        (1/(σ (B.W 0 (realTimeClamp r) w))^2) r) := by
  let H := fun (z : Ω × ℝ) => 1/(σ (B.W 0 (realTimeClamp z.2) z.1))^2
  have hfin r : realTimeClamp (T := (⊤:EReal)) r < ⊤ :=
    lt_of_le_of_lt (real_time_clamp_mono (le_max_right 0 r)) (changed_time_finite _ (le_max_left _ _))
  have hHc w : Continuous (fun r => H (w,r)) := by
    apply continuous_const.div
    · apply Continuous.pow
      apply hc.comp
      apply continuous_iff_continuousAt.mpr
      intro r
      exact ((B.martingale 0).path P B.F w _ (hfin r)).comp real_time_clamp_continuous.continuousAt
    · intro r
      exact pow_ne_zero _ (hn _)
  let A := fun t w => ∫ r in 0..(halfTimeReal t:ℝ),H (w,r)
  have hAr r (hr : 0 ≤ r) w : A (realTimeClamp r) w = ∫ s in 0..r,H (w,s) := by
    dsimp only [A]
    rw [changed_time_real r hr]
  refine ⟨A,?_,?_,?_,?_,?_⟩
  · intro t ht
    let R : ℝ := halfTimeReal t
    have hR : 0 ≤ R := (halfTimeReal t).property
    have ha r : Measurable[B.F (realTimeClamp r)] (fun w => H (w,r)) :=
      measurable_const.div ((hc.measurable.comp ((B.martingale 0).adapted P B.F _ (hfin r))).pow_const 2)
    have hprog := continuous_adapted_real_progressive B.F B.mono H R hR
      (fun r _ => ha r) (fun w => (hHc w).continuousOn)
    have hh := progressive_time_primitive_adapted R hR (fun r => B.F (realTimeClamp r.val)) H hprog ⟨R,hR,le_rfl⟩
    have he : realTimeClamp R = t := finite_clock_clamp_coordinate t ht
    change Measurable[B.F (realTimeClamp R)] (fun w => ∫ r in 0..R,H (w,r)) at hh
    rw [he] at hh
    exact hh
  · intro w t ht
    exact ((intervalIntegral.differentiable_integral_of_continuous (hHc w)).continuous.continuousAt).comp
      (changed_time_coordinate_continuousAt t ht)
  · intro w
    change (∫ r in (0:ℝ)..0,H (w,r)) = 0
    simp
  · intro w R
    obtain ⟨r,hr,hgt⟩ := divergent_positive_primitive (fun r => H (w,r)) (hHc w)
      (fun r => one_div_nonneg.mpr (sq_nonneg _)) (hdiv w) R
    exact ⟨realTimeClamp r,changed_time_finite r hr,by simpa only [hAr r hr] using hgt⟩
  · intro w r hr
    have hd := intervalIntegral.integral_hasDerivAt_right ((hHc w).intervalIntegrable 0 r)
      (hHc w).aestronglyMeasurable.stronglyMeasurableAtFilter (hHc w).continuousAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact hAr s hs.le w

end Asakura.Chapter7
