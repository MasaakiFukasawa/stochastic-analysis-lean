import Chapter5ClippedClockDensity
import Chapter5ProgressiveDriftVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter5
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

lemma clipped_driver_integral (g : ℝ → ℝ) (R r : ℝ) (hR : 0≤R) (hr : 0≤r) :
    (∫ s in 0..r,(Iic R).indicator g s)=∫ s in 0..min r R,g s := by
  rw [intervalIntegral.integral_of_le hr,integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic,
    intervalIntegral.integral_of_le (le_min hr hR)]
  have he : Iic R ∩ Ioc (0:ℝ) r=Ioc 0 (min r R) := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  rw [he]

lemma finite_prefix_time_min {T : EReal} [Fact (0≤T)]
    (R r : ℝ) (hR : 0≤R) (hr : 0≤r) (hrT : (r:EReal)≤T) :
    (finitePrefixTime (T := T) R hR (realTimeClamp r)).val=min r R := by
  change (min (realTimeClamp r:EReal) (R:EReal)).toReal=min r R
  rw [real_time_clamp_eq r hr hrT]
  by_cases h : r≤R
  · rw [min_eq_left (EReal.coe_le_coe h),EReal.toReal_coe,min_eq_left h]
  · rw [min_eq_right (EReal.coe_le_coe (le_of_not_ge h)),EReal.toReal_coe,min_eq_right (le_of_not_ge h)]

lemma clipped_driver_interval_integrable (g : ℝ → ℝ) (R r : ℝ) (hR : 0≤R) (hr : 0≤r)
    (hi : Integrable g (volume.restrict (Ioc 0 R))) :
    IntervalIntegrable ((Iic R).indicator g) volume 0 r := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mpr
  apply (integrable_indicator_iff measurableSet_Iic).mpr
  change Integrable g ((volume.restrict (Ioc 0 r)).restrict (Iic R))
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic R ∩ Ioc (0:ℝ) r ⊆ Ioc 0 R := fun s hs => ⟨hs.2.1,hs.1⟩
  exact hi.mono_measure (Measure.restrict_mono hs (le_refl volume))

end Asakura.Chapter5
