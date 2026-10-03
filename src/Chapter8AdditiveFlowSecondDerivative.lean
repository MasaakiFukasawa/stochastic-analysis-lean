import Chapter8SecondDerivativeIdentification

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Construct the additive solution, its first variation and its second
variation, and prove that both variations are actual initial derivatives.
This uses a continuous second derivative, without a third drift derivative. -/
theorem additive_flow_second_derivative_exists {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hDC : LipschitzWith C D)
    (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ))
    (W : ℝ → E) (hW : Continuous W) (T : ℝ) (hT : 0 ≤ T) :
    ∃ (X : E → ℝ → E) (J : E → ℝ → E →L[ℝ] E),
      (∀ x,Continuous (X x)) ∧ (∀ x,Continuous (J x)) ∧
      (∀ x y t,t∈Icc 0 T → ‖X x t-X y t‖ ≤ Real.exp (((L:ℝ)+1)*T)*‖x-y‖) ∧
      (∀ x t,t∈Icc 0 T → ∀ h,J x t h=h+∫ s in 0..t,D (X x s) (J x s h)) ∧
      (∀ x t,t∈Icc 0 T → X x t=x+(∫ s in 0..t,b (X x s))+W t) ∧
      (∀ x t,t∈Icc 0 T → HasFDerivAt (fun z => X z t) (J x t) x) ∧
      (∀ x t,t∈Icc 0 T → ‖J x t‖ ≤ Real.exp (((L:ℝ)+1)*T)) ∧
      ∀ x,∃ K : ℝ → E →L[ℝ] E →L[ℝ] E,Continuous K ∧
        (∀ t,t∈Icc 0 T → ∀ h k,K t h k=
          ∫ s in 0..t,D (X x s) (K s h k)+D₂ (X x s) (J x s h) (J x s k)) ∧
        ∀ t,t∈Icc 0 T → HasFDerivAt (fun z => J z t) (K t) x := by
  obtain ⟨X,hcX,hX,hLip,hJex⟩ := additive_flow_first_derivative_exists b D hD C L hDC hL hDb W hW T hT
  choose J hcJ hJ hJder using hJex
  let A := Real.exp (((L:ℝ)+1)*T)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hJb x : ∀ t,t∈Icc 0 T → ‖J x t‖ ≤ A :=
    additive_flow_derivative_bound X (J x) x T A hA hLip (hJder x)
  refine ⟨X,J,hcX,hcJ,hLip,hJ,hX,hJder,hJb,?_⟩
  intro x
  obtain ⟨K,hcK,hK⟩ := second_variation_exists T hT
    (fun s => D (X x s)) (fun s => D₂ (X x s)) (J x)
    (hDC.continuous.comp (hcX x)) (hcD₂.comp (hcX x)) (hcJ x) L (fun s => hDb _)
  refine ⟨K,hcK,hK,?_⟩
  intro t ht
  exact second_variation_is_derivative b D D₂ hD hD₂ hcD₂ C hDC X J W hcX hcJ x t A A L
    ht.1 hA hA (by exact_mod_cast hL) hDb
    (fun z s hs => hJb z s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun z s hs => hX z s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun z y s hs => hLip z y s ⟨hs.1,hs.2.trans ht.2⟩)
    (fun z s hs => hJ z s ⟨hs.1,hs.2.trans ht.2⟩)
    K hcK (fun s hs => hK s ⟨hs.1,hs.2.trans ht.2⟩)

end Asakura.Chapter8
