import Chapter12RapidCharacteristicDensity
import Chapter12WeightedCharacteristicBound
import Chapter12DecayNormChange

open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- Iterated weighted integration by parts is connected to the actual
law of F and a smooth density, with no density assumed in the argument. -/
theorem weighted_ibp_smooth_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ)
    (F : Ω → EuclideanSpace ℝ (Fin (d+1))) (hF : Measurable F)
    (H : ℕ → Fin (d+1) → Ω → ℝ)
    (he : ∀ k ξ i,(Complex.I*(ξ i:ℂ))^k*
      (∫ w,Complex.exp (Complex.I*(inner ℝ ξ (F w):ℂ)) ∂P)=
      ∫ w,(H k i w:ℂ)*Complex.exp (Complex.I*(inner ℝ ξ (F w):ℂ)) ∂P) :
    ∃ p : EuclideanSpace ℝ (Fin (d+1)) → ℝ,ContDiff ℝ ∞ p ∧ (∀ x,0≤p x) ∧
      P.map F=volume.withDensity (fun x => ENNReal.ofReal (p x)) := by
  let μ := P.map F
  letI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  let φ : EuclideanSpace ℝ (Fin (d+1)) → ℂ :=
    fun ξ => ∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ
  have hφ (ξ) : ‖φ ξ‖≤1 := by
    have hh := norm_integral_le_integral_norm (μ := μ)
      (fun y => Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)))
    simpa [φ,Complex.norm_exp] using hh
  have hmap (ξ) : φ ξ=∫ w,Complex.exp (Complex.I*(inner ℝ ξ (F w):ℂ)) ∂P := by
    exact integral_map hF.aemeasurable
      (show Continuous (fun y => Complex.exp (Complex.I*(inner ℝ ξ y:ℂ))) by fun_prop).aestronglyMeasurable
  have hd (k : ℕ) : ∃ A : ℝ,0≤A ∧ ∀ ξ,‖φ ξ‖≤A/(1+‖ξ‖)^k := by
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d+1) => ℝ)).symm
    apply decay_under_linear_equiv e φ k
    apply weighted_characteristic_decay P (fun ξ => φ (e ξ)) (fun w i => F w i) (H k)
      (fun ξ => hφ (e ξ))
    intro ξ i
    have hh := he k (e ξ) i
    rw [← hmap] at hh
    convert hh using 1
    · rfl
    · congr 1
      funext w
      congr 3
      simp [e,PiLp.inner_apply,RCLike.inner_apply,mul_comm]
  obtain ⟨p,hp,hpos,hμ,_⟩ := rapid_characteristic_density μ hd
  exact ⟨p,hp,hpos,hμ⟩

end Asakura.Chapter12
