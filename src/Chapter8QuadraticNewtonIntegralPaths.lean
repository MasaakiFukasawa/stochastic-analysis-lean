import Chapter8QuadraticNewtonPaths
import Chapter8CommonNoiseDifference

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

/-- The actual Newton integral equations imply contraction for a positive
quadratic force and every positive friction. -/
theorem quadratic_newton_integral_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (K : E →L[ℝ] E) (hs : K.toLinearMap.IsSymmetric)
    (hK : ∀ z≠0,0<⟪z,K z⟫) (δ : ℝ) (hδ : 0<δ) :
    ∃ (A : (E × E) ≃L[ℝ] WithLp 2
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
      (r : ℝ),0<r ∧
    ∀ (Q V Q' V' W : ℝ → E) (q₀ v₀ q₁ v₁ : E) (T : ℝ),
      0 ≤ T → Continuous Q → Continuous V → Continuous Q' → Continuous V' →
      (∀ t ∈ Icc 0 T, Q t = q₀ + ∫ s in (0:ℝ)..t,V s) →
      (∀ t ∈ Icc 0 T, Q' t = q₁ + ∫ s in (0:ℝ)..t,V' s) →
      (∀ t ∈ Icc 0 T, V t = v₀ + (∫ s in (0:ℝ)..t,-K (Q s)-δ • V s) + W t) →
      (∀ t ∈ Icc 0 T, V' t = v₁ + (∫ s in (0:ℝ)..t,-K (Q' s)-δ • V' s) + W t) →
      ∀ t ∈ Icc 0 T,
        ‖A (Q t-Q' t,V t-V' t)‖ ≤
          Real.exp (-r*t)*‖A (Q 0-Q' 0,V 0-V' 0)‖ := by
  obtain ⟨A,r,hr,hpath⟩ := quadratic_newton_path_contraction K hs hK δ hδ
  refine ⟨A,r,hr,?_⟩
  intro Q V Q' V' W q₀ v₀ q₁ v₁ T hT hQ hV hQ' hV' hIQ hIQ' hIV hIV'
  apply hpath (fun t => Q t-Q' t) (fun t => V t-V' t) T hT
    (hQ.sub hQ').continuousOn (hV.sub hV').continuousOn
  · intro t ht
    exact common_noise_integral_difference Q Q' (fun _ => 0) V V' q₀ q₁ T hV hV'
      (fun t ht => by simpa using hIQ t ht) (fun t ht => by simpa using hIQ' t ht) t ht
  · intro t ht
    have hh := common_noise_integral_difference V V' W
      (fun s => -K (Q s)-δ • V s) (fun s => -K (Q' s)-δ • V' s) v₀ v₁ T
      ((K.continuous.comp hQ).neg.sub (hV.const_smul δ))
      ((K.continuous.comp hQ').neg.sub (hV'.const_smul δ)) hIV hIV' t ht
    convert hh using 1
    rw [map_sub,smul_sub]
    abel
end Asakura.Chapter8
