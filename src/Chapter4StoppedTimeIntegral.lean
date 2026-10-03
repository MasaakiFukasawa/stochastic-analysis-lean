import Chapter4FinitePathLift

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1300000

/-- Ordinary integration obeys the same stopping-interval identity. -/
theorem time_integral_stochastic_interval
    {T : EReal} [Fact (0≤T)] (τ : ClosedTime T) (hτ : τ<⊤)
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T) (f : ℝ → ℝ) :
    (∫ r in 0..d,(Ioc (⊥ : ClosedTime T) τ).indicator (fun _ => f r) (realTimeClamp (T := T) r))=
      ∫ r in 0..(min τ (realTimeClamp (T := T) d):EReal).toReal,f r := by
  classical
  obtain ⟨q,hq,hqT,rfl⟩ := finite_closed_time_real τ hτ
  have hmin : (min (realTimeClamp (T := T) q) (realTimeClamp (T := T) d):EReal).toReal=min q d := by
    change (min (realTimeClamp (T := T) q:EReal) (realTimeClamp (T := T) d:EReal)).toReal=min q d
    rw [real_time_clamp_eq q hq hqT.le,real_time_clamp_eq d hd hdT.le]
    rcases le_total q d with h | h
    · rw [min_eq_left (EReal.coe_le_coe h),min_eq_left h,EReal.toReal_coe]
    · rw [min_eq_right (EReal.coe_le_coe h),min_eq_right h,EReal.toReal_coe]
  rw [hmin,intervalIntegral.integral_of_le hd,intervalIntegral.integral_of_le (le_min hq hd)]
  have he : (fun r => (Ioc (⊥ : ClosedTime T) (realTimeClamp (T := T) q)).indicator (fun _ => f r) (realTimeClamp (T := T) r))
      =ᵐ[volume.restrict (Ioc 0 d)] (Ioc (0:ℝ) q).indicator f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hrT : (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt hdT
    have hm : realTimeClamp (T := T) r∈Ioc (⊥ : ClosedTime T) (realTimeClamp (T := T) q) ↔ r∈Ioc (0:ℝ) q := by
      change ((0:EReal)<(realTimeClamp (T := T) r:EReal) ∧ (realTimeClamp (T := T) r:EReal)≤(realTimeClamp (T := T) q:EReal)) ↔ _
      rw [real_time_clamp_eq r hr.1.le hrT.le,real_time_clamp_eq q hq hqT.le]
      simp only [EReal.coe_pos,EReal.coe_le_coe_iff,mem_Ioc]
    by_cases h : r∈Ioc (0:ℝ) q
    · rw [indicator_of_mem h,indicator_of_mem (hm.mpr h)]
    · rw [indicator_of_notMem h,indicator_of_notMem (fun hx => h (hm.mp hx))]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc (0:ℝ) q ∩ Ioc 0 d = Ioc 0 (min q d) := by
    ext r
    simp only [mem_inter_iff,mem_Ioc,le_min_iff]
    tauto
  rw [hs]

end Asakura.Chapter4
