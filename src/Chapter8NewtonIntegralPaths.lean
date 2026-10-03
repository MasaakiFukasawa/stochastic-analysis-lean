import Chapter8CommonNoiseDifference

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter8

/-- Newton contraction follows from the integral equations and the stated
Hessian bounds. The averaged Hessian and both difference equations are proved,
not included as assumptions. -/
theorem newton_integral_path_contraction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (l u δ : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (hδ : Real.sqrt u - Real.sqrt l < δ) :
    ∃ b r : ℝ, 0 < r ∧ 0 < b+δ^2/4 ∧
    ∀ (g : E → E) (H : E → E →L[ℝ] E),
      (∀ x, HasFDerivAt g (H x) x) → Continuous H →
      (∀ x, (H x).toLinearMap.IsSymmetric) →
      (∀ x z, l*‖z‖^2 ≤ ⟪z,H x z⟫ ∧ ⟪z,H x z⟫ ≤ u*‖z‖^2) →
    ∀ (Q V Q' V' W : ℝ → E) (q₀ v₀ q₁ v₁ : E) (T : ℝ),
      0 ≤ T → Continuous Q → Continuous V → Continuous Q' → Continuous V' →
      (∀ t ∈ Icc 0 T, Q t = q₀ + ∫ s in (0:ℝ)..t,V s) →
      (∀ t ∈ Icc 0 T, Q' t = q₁ + ∫ s in (0:ℝ)..t,V' s) →
      (∀ t ∈ Icc 0 T, V t = v₀ + (∫ s in (0:ℝ)..t,-g (Q s)-δ • V s) + W t) →
      (∀ t ∈ Icc 0 T, V' t = v₁ + (∫ s in (0:ℝ)..t,-g (Q' s)-δ • V' s) + W t) →
      ∀ t ∈ Icc 0 T,
        newtonVectorEnergy δ b (Q t-Q' t) (V t-V' t) ≤
          Real.exp (-2*r*t)*newtonVectorEnergy δ b (Q 0-Q' 0) (V 0-V' 0) := by
  obtain ⟨b,r,hr,hp,hpath⟩ := vector_newton_contraction (E := E) l u δ hl hlu hδ
  refine ⟨b,r,hr,hp,?_⟩
  intro g H hd hH hsym hbound Q V Q' V' W q₀ v₀ q₁ v₁ T hT hQ hV hQ' hV' hIQ hIQ' hIV hIV'
  let K : ℝ → E →L[ℝ] E := fun t => ∫ s in (0:ℝ)..1,H (Q' t+s • (Q t-Q' t))
  have hKcont (t : ℝ) : Continuous (fun s : ℝ => H (Q' t+s • (Q t-Q' t))) :=
    hH.comp (by fun_prop)
  have hKsym (t : ℝ) : (K t).toLinearMap.IsSymmetric :=
    averaged_hessian_symmetric _ (hKcont t) (fun s => hsym _)
  have hKbound (t : ℝ) (z : E) : l*‖z‖^2 ≤ ⟪z,K t z⟫ ∧ ⟪z,K t z⟫ ≤ u*‖z‖^2 :=
    averaged_hessian_bounds _ (hKcont t) l u (fun s _ z => hbound _ z) z
  have hKeq (t : ℝ) : K t (Q t-Q' t) = g (Q t)-g (Q' t) :=
    averaged_hessian_gradient_difference g H hd hH (Q t) (Q' t)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  apply hpath (fun t => Q t-Q' t) (fun t => V t-V' t) (fun t => (K t).toLinearMap) T hT
    (hQ.sub hQ').continuousOn (hV.sub hV').continuousOn
    (fun t _ => hKsym t) (fun t _ z => hKbound t z)
  · intro t ht
    exact common_noise_integral_difference Q Q' (fun _ => 0) V V' q₀ q₁ T hV hV'
      (fun t ht => by simpa using hIQ t ht) (fun t ht => by simpa using hIQ' t ht) t ht
  · intro t ht
    have hh := common_noise_integral_difference V V' W
      (fun s => -g (Q s)-δ • V s) (fun s => -g (Q' s)-δ • V' s) v₀ v₁ T
      ((hgc.comp hQ).neg.sub (hV.const_smul δ))
      ((hgc.comp hQ').neg.sub (hV'.const_smul δ)) hIV hIV' t ht
    convert hh using 1
    change -K t (Q t-Q' t)-δ • (V t-V' t) = _
    rw [hKeq,smul_sub]
    abel

end Asakura.Chapter8
