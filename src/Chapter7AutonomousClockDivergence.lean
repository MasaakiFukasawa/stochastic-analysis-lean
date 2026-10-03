import Chapter7BrownianNullModification
import Chapter7BrownianOccupationWritten

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Brownian occupation supplies the divergent inverse-speed clock for
any continuous nonzero autonomous coefficient. A common null-set removal
makes the pathwise clock construction legitimate for every sample path. -/
theorem autonomous_clock_divergent_brownian
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hm : ∀ t,Measurable (B t)) (hc : ∀ w,Continuous (fun t => B t w))
    (σ : ℝ → ℝ) (hσ : Continuous σ) (hn : ∀ x,σ x ≠ 0) :
    ∃ BB : BrownianSystem P 1,
      ∀ w,(∫⁻ r in Ici (0:ℝ),ENNReal.ofReal
        (1/(σ (BB.W 0 (realTimeClamp r) w))^2)) = ∞ := by
  classical
  let BB := naturalBrownianSystem P B hB hm hc
  have hap x : 0 < 1/(σ x)^2 := one_div_pos.mpr (sq_pos_of_ne_zero (hn x))
  have hac : Continuous (fun x => 1/(σ x)^2) := continuous_const.div (hσ.pow 2) (fun x => pow_ne_zero _ (hn x))
  have hg : ∀ᵐ w ∂P,(∫⁻ r in Ici (0:ℝ),ENNReal.ofReal
      (1/(σ (BB.W 0 (realTimeClamp r) w))^2)) = ∞ := by
    filter_upwards [brownian_positive_clock_infinite P B hB hm hc _ hac hap] with w hw
    rw [← hw]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    have he : halfTimeReal (realTimeClamp r) = r.toNNReal := by
      apply Subtype.ext
      change (halfTimeReal (realTimeClamp r):ℝ) = (r.toNNReal:ℝ)
      rw [changed_time_real r hr,Real.coe_toNNReal r hr]
    change ENNReal.ofReal (1/(σ (B (halfTimeReal (realTimeClamp r)) w))^2) = _
    rw [he]
  let good := fun w => (∫⁻ r in Ici (0:ℝ),ENNReal.ofReal
      (1/(σ (BB.W 0 (realTimeClamp r) w))^2)) = ∞
  let N := toMeasurable P {w | ¬good w}
  have hNm : MeasurableSet[m] N := measurableSet_toMeasurable _ _
  have hNz : P N = 0 := by rw [measure_toMeasurable]; exact ae_iff.mp hg
  let Y := zeroOnNullBrownian P BB N hNm hNz
  refine ⟨Y,?_⟩
  intro w
  by_cases hw : w ∈ N
  · change (∫⁻ r in Ici (0:ℝ),ENNReal.ofReal (1/(σ (if w ∈ N then 0 else BB.W 0 (realTimeClamp r) w))^2)) = ∞
    simp only [ite_eq_left hw,lintegral_const,Measure.restrict_apply_univ,Real.volume_Ici,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (hap 0)))]
  · have hgood : good w := not_not.mp (fun hh => hw (subset_toMeasurable P {w | ¬good w} hh))
    change (∫⁻ r in Ici (0:ℝ),ENNReal.ofReal (1/(σ (if w ∈ N then 0 else BB.W 0 (realTimeClamp r) w))^2)) = ∞
    simpa only [ite_eq_right hw] using hgood

end Asakura.Chapter7
