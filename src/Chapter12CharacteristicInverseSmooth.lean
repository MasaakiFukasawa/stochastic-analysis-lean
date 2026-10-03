import Chapter12RapidDecayFourierSmooth

open MeasureTheory Real
open scoped ContDiff RealInnerProductSpace FourierTransform
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem characteristic_inverse_smooth {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (φ : E → ℂ) (hm : AEStronglyMeasurable φ volume)
    (hd : ∀ k : ℕ,∃ A : ℝ,0≤A ∧ ∀ ξ,‖φ ξ‖≤A/(1+‖ξ‖)^k) :
    ContDiff ℝ ∞ (fun x => ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ) := by
  let L : E →L[ℝ] E →L[ℝ] ℝ := (1/(2*π)) • innerSL ℝ
  have hh := rapid_decay_fourier_smooth volume L φ hm hd
  have he : VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ φ=
      (fun x => ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*φ ξ) := by
    funext x
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    change Complex.exp (((-2*π*((1/(2*π))*inner ℝ ξ x):ℝ):ℂ)*Complex.I)*φ ξ=_
    congr 2
    have hr : -2*π*((1/(2*π))*inner ℝ ξ x)= -inner ℝ ξ x := by field_simp <;> ring
    rw [hr,Complex.ofReal_neg]
    ring
  rw [he] at hh
  exact hh

end Asakura.Chapter12
