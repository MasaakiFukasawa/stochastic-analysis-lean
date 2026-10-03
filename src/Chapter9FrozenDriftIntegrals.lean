import Chapter9StoppedGeneratorCutoff

open MeasureTheory Set
namespace Asakura.Chapter9
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter5
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Freezing at a finite endpoint corresponds to cutting off the time
 density. This includes the state factor in the product formula. -/
theorem frozen_weighted_drift_integral (a z : ℝ → ℝ) (b r : ℝ) (hb : 0≤b) (hr : 0≤r) :
    (∫ u in 0..r,z (finitePrefixTime (T := (⊤:EReal)) b hb (realTimeClamp u)).val*
      (Iic b).indicator a u)=∫ u in 0..min r b,z u*a u := by
  have he : (∫ u in 0..r,z (finitePrefixTime (T := (⊤:EReal)) b hb (realTimeClamp u)).val*
      (Iic b).indicator a u)=∫ u in 0..r,(Iic b).indicator (fun u => z u*a u) u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0≤u := (uIcc_of_le hr ▸ hu).1
    dsimp only
    rw [finite_prefix_time_min b u hb hu0 le_top]
    by_cases hub : u∈Iic b
    · rw [Set.indicator_of_mem hub,Set.indicator_of_mem hub,min_eq_left hub]
    · rw [Set.indicator_of_notMem hub,Set.indicator_of_notMem hub,mul_zero]
  rw [he,clipped_driver_integral _ b r hb hr]

theorem frozen_drift_integral (a : ℝ → ℝ) (b r : ℝ) (hb : 0≤b) (hr : 0≤r) :
    (∫ u in 0..r,(Iic b).indicator a u)=
      ∫ u in 0..(finitePrefixTime (T := (⊤:EReal)) b hb (realTimeClamp r)).val,a u := by
  rw [clipped_driver_integral _ b r hb hr,finite_prefix_time_min b r hb hr le_top]
end Asakura.Chapter9
