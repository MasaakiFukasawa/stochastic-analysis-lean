import Chapter12WeightedCharacteristicBound
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000

theorem weighted_characteristic_parts {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (X G:Ω → ℝ) (hX:AEStronglyMeasurable X P) (hG:Integrable G P) :
    (∫w,(G w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P).re=∫w,G w*Real.cos (X w) ∂P ∧
    (∫w,(G w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P).im=∫w,G w*Real.sin (X w) ∂P := by
  have hm:AEStronglyMeasurable (fun w => Complex.exp (Complex.I*(X w:ℂ))) P :=
    (show Continuous (fun x:ℝ => Complex.exp (Complex.I*(x:ℂ))) by fun_prop).comp_aestronglyMeasurable hX
  have hi:Integrable (fun w => (G w:ℂ)*Complex.exp (Complex.I*(X w:ℂ))) P :=
    hG.ofReal.mul_bdd (c:=1) hm (Filter.Eventually.of_forall (fun w => by simp [Complex.norm_exp]))
  constructor
  · have hh := (integral_re hi).symm
    simpa [Complex.mul_re,Complex.exp_re] using hh
  · have hh := (integral_im hi).symm
    simpa [Complex.mul_im,Complex.exp_im] using hh

theorem characteristic_from_sin_cos_ibp {Ω:Type*} [MeasurableSpace Ω]
    (P:Measure Ω) (X G Z:Ω → ℝ) (hX:AEStronglyMeasurable X P)
    (hG:Integrable G P) (hZ:Integrable Z P) (c:ℝ)
    (hc:(∫w,Z w*Real.cos (X w) ∂P)= -c*(∫w,G w*Real.sin (X w) ∂P))
    (hs:(∫w,Z w*Real.sin (X w) ∂P)= c*(∫w,G w*Real.cos (X w) ∂P)) :
    (∫w,(Z w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P)=
      (Complex.I*(c:ℂ))*(∫w,(G w:ℂ)*Complex.exp (Complex.I*(X w:ℂ)) ∂P) := by
  obtain ⟨hGr,hGi⟩ := weighted_characteristic_parts P X G hX hG
  obtain ⟨hZr,hZi⟩ := weighted_characteristic_parts P X Z hX hZ
  apply Complex.ext
  · simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,sub_zero,zero_add,hZr,hGi]
    simpa only [neg_mul] using hc
  · simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_sub,sub_zero,zero_add,hZi,hGr]
    exact hs
end Asakura.Chapter12
#print axioms Asakura.Chapter12.characteristic_from_sin_cos_ibp
