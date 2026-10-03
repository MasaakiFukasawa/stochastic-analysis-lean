import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Chapter13HJMPrimitive

open MeasureTheory Set
namespace Asakura.Chapter13
set_option maxHeartbeats 1800000

theorem primitive_product (f g:ℝ → ℝ) (a b:ℝ)
    (hf:IntervalIntegrable f volume a b) (hg:IntervalIntegrable g volume a b) :
    (∫s in a..b,f s)*(∫s in a..b,g s)=
      (∫s in a..b,f s*(∫v in a..s,g v))+(∫s in a..b,(∫v in a..s,f v)*g s) := by
  have hF:=hf.absolutelyContinuousOnInterval_intervalIntegral (c:=a) left_mem_uIcc
  have hG:=hg.absolutelyContinuousOnInterval_intervalIntegral (c:=a) left_mem_uIcc
  have hp:=hF.integral_deriv_mul_eq_sub hG
  have he:(∫s in a..b,deriv (fun t => ∫v in a..t,f v) s*(∫v in a..s,g v)+
      (∫v in a..s,f v)*deriv (fun t => ∫v in a..t,g v) s)=
      ∫s in a..b,f s*(∫v in a..s,g v)+(∫v in a..s,f v)*g s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [_root_.IntervalIntegrable.ae_hasDerivAt_integral hf,
      _root_.IntervalIntegrable.ae_hasDerivAt_integral hg] with s hs ht hsi
    have hsu:=uIoc_subset_uIcc hsi
    rw [(hs hsu a (left_mem_uIcc)).deriv,(ht hsu a (left_mem_uIcc)).deriv]
  rw [he,intervalIntegral.integral_add (hf.mul_continuousOn hG.continuousOn)
    (hg.continuousOn_mul hF.continuousOn)] at hp
  simpa using hp.symm

/-- The deterministic integration by parts used componentwise in Cheyette's state formula. -/
theorem cheyette_primitive_kernel (f g:ℝ → ℝ) (a b K:ℝ)
    (hf:IntervalIntegrable f volume a b) (hg:IntervalIntegrable g volume a b) :
    (∫s in a..b,f s*(K-∫v in a..s,g v))=
      (∫s in a..b,f s)*(K-∫v in a..b,g v)+(∫s in a..b,(∫v in a..s,f v)*g s) := by
  have hG:=hg.absolutelyContinuousOnInterval_intervalIntegral (c:=a) left_mem_uIcc
  have hi:=hf.mul_continuousOn hG.continuousOn
  have hp:=primitive_product f g a b hf hg
  simp only [mul_sub]
  rw [intervalIntegral.integral_sub (hf.mul_const K) hi,intervalIntegral.integral_mul_const]
  linarith

theorem primitive_square_integral (g:ℝ → ℝ) (a b:ℝ)
    (hg:IntervalIntegrable g volume a b) :
    (∫s in a..b,g s*(∫v in a..s,g v))=(∫s in a..b,g s)^2/2 := by
  have h:=primitive_product g g a b hg hg
  have he:(fun s => (∫v in a..s,g v)*g s)=(fun s => g s*(∫v in a..s,g v)) := by funext s;ring
  rw [he] at h
  nlinarith
end Asakura.Chapter13
#print axioms Asakura.Chapter13.primitive_product
#print axioms Asakura.Chapter13.cheyette_primitive_kernel
#print axioms Asakura.Chapter13.primitive_square_integral
