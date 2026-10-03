import Chapter7ContinuousModulus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The remainder after freezing a continuous drift at the left endpoint,
controlled by the actual compact-interval modulus of continuity. -/
theorem drift_interval_remainder (T : ℝ) (b : ℝ → ℝ)
    (hb : ContinuousOn b (Icc 0 T)) (s t : Icc (0:ℝ) T)
    (hst : s ≤ t) (h : ℝ≥0) (hmesh : (t:ℝ)-s ≤ (h:ℝ)) :
    let f : C(Icc (0:ℝ) T,ℝ) := ⟨fun x => b x,hb.restrict⟩
    |(∫ r in (s:ℝ)..(t:ℝ),b r)-((t:ℝ)-s)*b s| ≤
      ((t:ℝ)-s)*‖modulusPath f h‖ := by
  let f : C(Icc (0:ℝ) T,ℝ) := ⟨fun x => b x,hb.restrict⟩
  have hstR : (s:ℝ) ≤ t := hst
  have hib : IntervalIntegrable b volume (s:ℝ) t :=
    (hb.mono (fun r hr => ⟨s.property.1.trans hr.1,hr.2.trans t.property.2⟩)).intervalIntegrable_of_Icc hstR
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (s:ℝ)) (b := (t:ℝ)) (f := fun r => b r-b s) (C := ‖modulusPath f h‖) (by
      intro r hr
      rw [uIoc_of_le hstR] at hr
      let x : Icc (0:ℝ) T := ⟨r,⟨s.property.1.trans hr.1.le,hr.2.trans t.property.2⟩⟩
      have hdist : dist x s ≤ (h:ℝ) := by
        change |r-(s:ℝ)| ≤ (h:ℝ)
        rw [abs_of_nonneg (sub_nonneg.mpr hr.1.le)]
        exact (sub_le_sub_right hr.2 _).trans hmesh
      have hm := modulusPath_bound f h x s hdist
      change |b r-b s| ≤ ‖modulusPath f h‖ at hm
      simpa only [Real.norm_eq_abs] using hm)
  rw [intervalIntegral.integral_sub hib intervalIntegrable_const,intervalIntegral.integral_const] at hbound
  simpa only [smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hstR),mul_comm] using hbound

end Asakura.Chapter7
