import Chapter8IntervalPairs
import Chapter8VariationalStability
import Chapter8SecondVariationConstruction

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Identify the second variation with the derivative of J by applying
the C1 integral-equation argument to the augmented state (X,J). -/
theorem second_variation_is_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C : ℝ≥0) (hDC : LipschitzWith C D)
    (X : E → ℝ → E) (J : E → ℝ → E →L[ℝ] E) (W : ℝ → E)
    (hcX : ∀ z,Continuous (X z)) (hcJ : ∀ z,Continuous (J z))
    (x : E) (T A B L : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0<L)
    (hDb : ∀ z,‖D z‖ ≤ L) (hJb : ∀ z s,s∈Icc 0 T → ‖J z s‖ ≤ B)
    (hX : ∀ z s,s∈Icc 0 T → X z s=z+(∫ r in 0..s,b (X z r))+W s)
    (hLip : ∀ z y s,s∈Icc 0 T → ‖X z s-X y s‖ ≤ A*‖z-y‖)
    (hJ : ∀ z s,s∈Icc 0 T → ∀ h,J z s h=h+∫ r in 0..s,D (X z r) (J z r h))
    (K : ℝ → E →L[ℝ] E →L[ℝ] E) (hcK : Continuous K)
    (hK : ∀ s,s∈Icc 0 T → ∀ h k,K s h k=
      ∫ r in 0..s,D (X x r) (K r h k)+D₂ (X x r) (J x r h) (J x r k)) :
    HasFDerivAt (fun z => J z T) (K T) x := by
  let F := E × (E →L[ℝ] E)
  let Z := fun z s => (X z s,J z s)
  let a := fun p : F => (b p.1,D p.1*p.2)
  let Γ := fun s => (J x s).prod (K s)
  let I : E →L[ℝ] F := (ContinuousLinearMap.id ℝ E).prod 0
  have hbc : Continuous b := continuous_iff_continuousAt.mpr (fun z => (hD z).continuousAt)
  have hcZ z : Continuous (Z z) := (hcX z).prodMk (hcJ z)
  have hcΓ : Continuous Γ := by
    have hh : Continuous (fun p : (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) => p.1.prod p.2) :=
      (ContinuousLinearMap.prodₗᵢ ℝ).continuous
    exact hh.comp ((hcJ x).prodMk hcK)
  have haugc := augmented_derivative_continuous D D₂ hDC.continuous hcD₂
  have hncont : Continuous (fun s : ℝ => ‖augmentedDerivative D D₂ (Z x s)‖) :=
    (show Continuous (fun q : F →L[ℝ] F => ‖q‖) from continuous_norm (E := F →L[ℝ] F)).comp (haugc.comp (hcZ x))
  obtain ⟨R,hR⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn hncont.continuousOn
  have hRpos : 0<max R 0+1 := by positivity
  have hJop z s (hs : s∈Icc 0 T) : J z s=1+∫ r in 0..s,D (X z r)*J z r := by
    apply ContinuousLinearMap.ext
    intro h
    rw [hJ z s hs h]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.intervalIntegral_apply (φ := fun r => D (X z r)*J z r)
      (((hDC.continuous.comp (hcX z)).mul (hcJ z)).intervalIntegrable 0 s)]
    rfl
  have hZe z s (hs : s∈Icc 0 T) : Z z s=I z+(0,1)+(∫ r in 0..s,a (Z z r))+(W s,0) := by
    rw [show (∫ r in 0..s,a (Z z r))=(∫ r in 0..s,b (X z r),∫ r in 0..s,D (X z r)*J z r) from
      interval_integral_pair _ _ 0 s (hbc.comp (hcX z)) ((hDC.continuous.comp (hcX z)).mul (hcJ z))]
    apply Prod.ext
    · change X z s=(z+0+(∫ r in 0..s,b (X z r)))+W s
      simpa only [add_zero] using hX z s hs
    · change J z s=0+1+(∫ r in 0..s,D (X z r)*J z r)+0
      simpa only [zero_add,add_zero] using hJop z s hs
  let A' := (C:ℝ)*A*B*T*Real.exp (L*T)
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  have hJL := variational_initial_stability D C hDC X J hcX hcJ T A B L hT hA hB hL hDb hJb hLip hJ
  have hZLip h s (hs : s∈Icc 0 T) : ‖Z (x+h) s-Z x s‖ ≤ (A+A')*‖h‖ := by
    have h1 := hLip (x+h) x s hs
    have h2 := hJL (x+h) x s hs
    simp only [add_sub_cancel_left] at h1 h2
    change max ‖X (x+h) s-X x s‖ ‖J (x+h) s-J x s‖ ≤ _
    apply max_le
    · exact h1.trans (by nlinarith [norm_nonneg h])
    · exact h2.trans (by dsimp only [A']; nlinarith [norm_nonneg h])
  have hΓe s (hs : s∈Icc 0 T) (h : E) : Γ s h=I h+∫ r in 0..s,augmentedDerivative D D₂ (Z x r) (Γ r h) := by
    have hc1 : Continuous (fun r => D (X x r) (J x r h)) :=
      (hDC.continuous.comp (hcX x)).clm_apply ((hcJ x).clm_apply continuous_const)
    have hc2 : Continuous (fun r => D₂ (X x r) (J x r h)*J x r+D (X x r)*K r h) :=
      (((hcD₂.comp (hcX x)).clm_apply ((hcJ x).clm_apply continuous_const)).mul (hcJ x)).add
      ((hDC.continuous.comp (hcX x)).mul (hcK.clm_apply continuous_const))
    change (J x s h,K s h)=(h,0)+∫ r in 0..s,
      (D (X x r) (J x r h),D₂ (X x r) (J x r h)*J x r+D (X x r)*K r h)
    rw [interval_integral_pair _ _ 0 s hc1 hc2]
    apply Prod.ext
    · exact hJ x s hs h
    · change K s h=0+∫ r in 0..s,D₂ (X x r) (J x r h)*J x r+D (X x r)*K r h
      rw [zero_add]
      apply ContinuousLinearMap.ext
      intro k
      rw [hK s hs h k,ContinuousLinearMap.intervalIntegral_apply
        (φ := fun r => D₂ (X x r) (J x r h)*J x r+D (X x r)*K r h) (hc2.intervalIntegrable 0 s)]
      apply intervalIntegral.integral_congr
      intro r _
      change D (X x r) (K r h k)+D₂ (X x r) (J x r h) (J x r k)=
        D₂ (X x r) (J x r h) (J x r k)+D (X x r) (K r h k)
      exact add_comm _ _
  have hd := continuous_variational_derivative a (augmentedDerivative D D₂)
    (augmented_drift_derivative b D D₂ hD hD₂) haugc I (0,1) Z (fun s => (W s,0)) hcZ
    x T (A+A') (max R 0+1) hT (add_nonneg hA hA') hRpos
    (fun s hs => (by
      have hh : ‖augmentedDerivative D D₂ (Z x s)‖ ≤ R :=
        (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hR s hs)
      exact hh.trans (by linarith [le_max_left R 0]))) hZe hZLip Γ hcΓ hΓe
  exact hd.snd

end Asakura.Chapter8
