import Chapter2WeightedHilbert
import FullAuditBVMartingaleWritten

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The cumulative integral of an integrable function against an atomless
measure is continuous. This proves the pathwise continuity used in density. -/
theorem continuous_cumulative_integral (μ : Measure ℝ) [NullSingletonClass μ]
    (g : ℝ → ℝ) (hg : Integrable g μ) : Continuous (fun t => ∫ x in Iic t, g x ∂μ) := by
  classical
  have he (t) : (∫ x in Iic t, g x ∂μ) = ∫ x, (Iic t).indicator g x ∂μ :=
    (integral_indicator measurableSet_Iic).symm
  simp only [he]
  apply continuous_iff_continuousAt.2
  intro t
  refine continuousAt_of_dominated (bound := fun x => ‖g x‖)
    (.of_forall fun s => hg.aestronglyMeasurable.indicator measurableSet_Iic) ?_ hg.norm ?_
  · exact .of_forall fun s => .of_forall fun x => by
      by_cases h : x ∈ Iic s <;> simp [Set.indicator,h]
  · have hne : ∀ᵐ x ∂μ, x ≠ t := by simp [ae_iff]
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with hxt | htx
    · change Tendsto (fun s => (Iic s).indicator g x) (𝓝 t) (𝓝 ((Iic t).indicator g x))
      rw [indicator_of_mem (show x ∈ Iic t from hxt.le)]
      apply tendsto_const_nhds.congr'
      filter_upwards [lt_mem_nhds hxt] with s hs
      simp only [indicator_of_mem (show x ∈ Iic s from hs.le)]
    · change Tendsto (fun s => (Iic s).indicator g x) (𝓝 t) (𝓝 ((Iic t).indicator g x))
      rw [indicator_of_notMem (show x ∉ Iic t from not_le_of_gt htx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [gt_mem_nhds htx] with s hs
      simp only [indicator_of_notMem (show x ∉ Iic s from not_le_of_gt hs)]

/-- The positive and negative parts give increasing continuous paths whose
difference is the cumulative integral, exactly as used for finite variation. -/
theorem cumulative_integral_continuous_jordan (μ : Measure ℝ) [NullSingletonClass μ]
    (g : ℝ → ℝ) (hg : Integrable g μ) :
    ∃ U V : ℝ → ℝ, Continuous U ∧ Continuous V ∧ Monotone U ∧ Monotone V ∧
      ∀ t, (∫ x in Iic t, g x ∂μ) = U t-V t := by
  let gp := fun x => max (g x) 0
  let gn := fun x => max (-g x) 0
  have hgp : Integrable gp μ := hg.pos_part
  have hgn : Integrable gn μ := hg.neg_part
  refine ⟨fun t => ∫ x in Iic t, gp x ∂μ,fun t => ∫ x in Iic t, gn x ∂μ,
    continuous_cumulative_integral μ gp hgp,continuous_cumulative_integral μ gn hgn,?_,?_,?_⟩
  · intro s t hst
    exact setIntegral_mono_set hgp.integrableOn
      (.of_forall fun x => le_max_right _ _) (.of_forall fun x hx => hx.trans hst)
  · intro s t hst
    exact setIntegral_mono_set hgn.integrableOn
      (.of_forall fun x => le_max_right _ _) (.of_forall fun x hx => hx.trans hst)
  · intro t
    rw [← integral_sub hgp.integrableOn hgn.integrableOn]
    apply integral_congr_ae
    exact .of_forall fun x => (max_zero_sub_max_neg_zero_eq_self (g x)).symm

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.continuous_cumulative_integral
#print axioms Asakura.Chapter2Complete.cumulative_integral_continuous_jordan
