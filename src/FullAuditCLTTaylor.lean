import FullAuditCLTRemainders
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit

/-- Taylor's integral formula along a segment, requiring two-sided derivatives
only in its interior. This permits the heat-kernel time coordinate to end at 0. -/
theorem clt_taylor_segment (f d q : ℝ → ℝ)
    (hf : ContinuousOn f (Icc 0 1)) (hd : ContinuousOn d (Icc 0 1))
    (hq : ContinuousOn q (Icc 0 1))
    (hfd : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt f (d s) s)
    (hdq : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt d (q s) s) :
    f 1 = f 0 + d 0 + ∫ s in (0:ℝ)..1, q s * (1-s) := by
  have hdu : ContinuousOn d (uIcc 0 1) := by simpa only [uIcc_of_le zero_le_one] using hd
  have hqu : ContinuousOn q (uIcc 0 1) := by simpa only [uIcc_of_le zero_le_one] using hq
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hf hfd hdu.intervalIntegrable
  have hj := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun s : ℝ => 1-s) (u' := fun _ => -1) (v := d) (v' := q)
    (by fun_prop) hdu (fun s _ => by simpa using (hasDerivAt_id s).const_sub 1)
    (by simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using hdq)
    (intervalIntegrable_const) hqu.intervalIntegrable
  simp only [sub_self,zero_mul,sub_zero,one_mul,neg_one_mul,intervalIntegral.integral_neg,hi] at hj
  have he : (∫ s in (0:ℝ)..1, q s*(1-s)) = ∫ s in (0:ℝ)..1, (1-s)*q s := by
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [he]
  linarith

/-- The exact two scalar weights in the Hessian-remainder calculation. -/
theorem clt_weight_integrals :
    (∫ s in (0:ℝ)..1, 1-s) = 1/2 ∧ (∫ s in (0:ℝ)..1, s*(1-s)) = 1/6 := by
  have hi : IntervalIntegrable (fun s : ℝ => s) volume 0 1 := continuous_id.intervalIntegrable _ _
  have hsq : IntervalIntegrable (fun s : ℝ => s^2) volume 0 1 := (continuous_id.pow 2).intervalIntegrable _ _
  constructor
  · rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    norm_num
  · have he : (fun s : ℝ => s*(1-s)) = fun s => s-s^2 := by funext s; ring
    rw [he,intervalIntegral.integral_sub hi hsq]
    norm_num [integral_pow]

/-- A bounded Hessian entry integrated against the Taylor weight. -/
theorem clt_weighted_bound (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 1))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ s ∈ Icc (0:ℝ) 1, |F s| ≤ K) :
    |∫ s in (0:ℝ)..1, F s*(1-s)| ≤ K/2 := by
  have hFu : ContinuousOn F (uIcc 0 1) := by simpa only [uIcc_of_le zero_le_one] using hF
  have hi : IntervalIntegrable (fun s => F s*(1-s)) volume 0 1 :=
    (hFu.mul (by fun_prop)).intervalIntegrable
  calc
    _ ≤ ∫ s in (0:ℝ)..1, |F s*(1-s)| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := fun s => F s*(1-s)) zero_le_one
    _ ≤ ∫ s in (0:ℝ)..1, K*(1-s) := by
      apply intervalIntegral.integral_mono_on zero_le_one hi.norm (by apply Continuous.intervalIntegrable; fun_prop)
      intro s hs
      have hs1 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hs1]
      exact mul_le_mul_of_nonneg_right (hbound s hs) hs1
    _ = K/2 := by rw [intervalIntegral.integral_const_mul,clt_weight_integrals.1]; ring

/-- The extra factor s in the third-derivative bound yields exactly 1/6. -/
theorem clt_weighted_linear_bound (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 1))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ s ∈ Icc (0:ℝ) 1, |F s| ≤ K*s) :
    |∫ s in (0:ℝ)..1, F s*(1-s)| ≤ K/6 := by
  have hFu : ContinuousOn F (uIcc 0 1) := by simpa only [uIcc_of_le zero_le_one] using hF
  have hi : IntervalIntegrable (fun s => F s*(1-s)) volume 0 1 :=
    (hFu.mul (by fun_prop)).intervalIntegrable
  calc
    _ ≤ ∫ s in (0:ℝ)..1, |F s*(1-s)| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := fun s => F s*(1-s)) zero_le_one
    _ ≤ ∫ s in (0:ℝ)..1, K*(s*(1-s)) := by
      apply intervalIntegral.integral_mono_on zero_le_one hi.norm (by apply Continuous.intervalIntegrable; fun_prop)
      intro s hs
      have hs1 : 0 ≤ 1-s := sub_nonneg.mpr hs.2
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hs1,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hbound s hs) hs1
    _ = K/6 := by rw [intervalIntegral.integral_const_mul,clt_weight_integrals.2]; ring

end Asakura.FullAudit
