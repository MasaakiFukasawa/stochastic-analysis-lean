import Chapter12GaussianMatrixMoment

open MeasureTheory
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Averaging scalar estimates over an auxiliary Gaussian projection.
Tonelli is used before integrability of the joint expression is known. -/
theorem projection_averaging_bound {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [SigmaFinite P] [SigmaFinite Q]
    (A B : Ξ → Ω → ℝ) (C D : Ω → ℝ)
    (hAm : Measurable (Function.uncurry A)) (hBm : Measurable (Function.uncurry B))
    (hAn : ∀ z x,0≤A z x) (hBn : ∀ z x,0≤B z x)
    (hCn : ∀ x,0≤C x) (hDn : ∀ x,0≤D x)
    (hAP : ∀ z,Integrable (A z) P) (hBP : ∀ z,Integrable (B z) P)
    (hAQ : ∀ x,Integrable (fun z => A z x) Q) (hBQ : ∀ x,Integrable (fun z => B z x) Q)
    (hC : Integrable C P) (hD : Integrable D P)
    (c K : ℝ) (hc : 0<c) (hK : 0≤K)
    (hleft : ∀ x,(∫ z,A z x ∂Q)=c*C x)
    (hright : ∀ x,(∫ z,B z x ∂Q)≤c*D x)
    (hscalar : ∀ z,(∫ x,A z x ∂P)≤K*(∫ x,B z x ∂P)) :
    (∫ x,C x ∂P)≤K*(∫ x,D x ∂P) := by
  have haP z : (∫⁻ x,ENNReal.ofReal (A z x) ∂P)=ENNReal.ofReal (∫ x,A z x ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hAP z) (ae_of_all P (hAn z))).symm
  have hbP z : (∫⁻ x,ENNReal.ofReal (B z x) ∂P)=ENNReal.ofReal (∫ x,B z x ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hBP z) (ae_of_all P (hBn z))).symm
  have haQ x : (∫⁻ z,ENNReal.ofReal (A z x) ∂Q)=ENNReal.ofReal c*ENNReal.ofReal (C x) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hAQ x) (ae_of_all Q (fun z => hAn z x)),hleft,
      ENNReal.ofReal_mul hc.le]
  have hbQ x : (∫⁻ z,ENNReal.ofReal (B z x) ∂Q)≤ENNReal.ofReal c*ENNReal.ofReal (D x) := by
    rw [←ofReal_integral_eq_lintegral_ofReal (hBQ x) (ae_of_all Q (fun z => hBn z x)),
      ←ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (hright x)
  have hs z : (∫⁻ x,ENNReal.ofReal (A z x) ∂P)≤
      ENNReal.ofReal K*(∫⁻ x,ENNReal.ofReal (B z x) ∂P) := by
    rw [haP,hbP,←ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hscalar z)
  have hh : ENNReal.ofReal c*ENNReal.ofReal (∫ x,C x ∂P)≤
      ENNReal.ofReal K*(ENNReal.ofReal c*ENNReal.ofReal (∫ x,D x ∂P)) := by
    calc
      _ = ∫⁻ x,∫⁻ z,ENNReal.ofReal (A z x) ∂Q ∂P := by
        simp_rw [haQ]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ←ofReal_integral_eq_lintegral_ofReal hC (ae_of_all P hCn)]
      _ = ∫⁻ z,∫⁻ x,ENNReal.ofReal (A z x) ∂P ∂Q :=
        (lintegral_lintegral_swap hAm.ennreal_ofReal.aemeasurable).symm
      _ ≤ ∫⁻ z,ENNReal.ofReal K*(∫⁻ x,ENNReal.ofReal (B z x) ∂P) ∂Q := lintegral_mono hs
      _ = ENNReal.ofReal K*(∫⁻ x,∫⁻ z,ENNReal.ofReal (B z x) ∂Q ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_lintegral_swap hBm.ennreal_ofReal.aemeasurable]
      _ ≤ ENNReal.ofReal K*(∫⁻ x,ENNReal.ofReal c*ENNReal.ofReal (D x) ∂P) :=
        mul_le_mul' le_rfl (lintegral_mono hbQ)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ←ofReal_integral_eq_lintegral_ofReal hD (ae_of_all P hDn)]
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le,ENNReal.toReal_ofReal hK,
    ENNReal.toReal_ofReal (integral_nonneg hCn),ENNReal.toReal_ofReal (integral_nonneg hDn)] at hr
  exact (mul_le_mul_iff_right₀ hc).mp (by nlinarith [hr])

end Asakura.Chapter12
