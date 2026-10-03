import Chapter8AdditiveFlowSecondDerivative
import Chapter8FirstVariationContinuity
import Chapter8SecondVariationContinuity
import Chapter8AdditiveUniqueness
import Chapter8SecondVariationBound

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
set_option maxHeartbeats 3200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

/-- The solution and both variational derivatives as jointly continuous
functions of the initial point and the continuous forcing path. This
supplies measurability of the variational processes used in expectations. -/
theorem canonical_smooth_additive_flow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b : E → E) (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ z,HasFDerivAt b (D z) z) (hD₂ : ∀ z,HasFDerivAt D (D₂ z) z)
    (hcD₂ : Continuous D₂) (C L : ℝ≥0) (hDC : LipschitzWith C D)
    (hL : 0<L) (hDb : ∀ z,‖D z‖ ≤ (L:ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ (S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
      (J : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E →L[ℝ] E))
      (K : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E →L[ℝ] E →L[ℝ] E)),
      Continuous S ∧ Continuous J ∧ Continuous K ∧
      (∀ p t,S p t=p.1+(∫ s in 0..t.val,b (S p (projIcc 0 T hT s)))+p.2 t) ∧
      (∀ x w t,HasFDerivAt (fun z => S (z,w) t) (J (x,w) t) x) ∧
      (∀ x w t,HasFDerivAt (fun z => J (z,w) t) (K (x,w) t) x) ∧
      (∀ p t,‖J p t‖ ≤ Real.exp (((L:ℝ)+1)*T)) ∧
      ∀ p t,‖K p t‖ ≤ (C:ℝ)*Real.exp (((L:ℝ)+1)*T)^2*T*Real.exp ((L:ℝ)*T) := by
  have hex (w : C(Icc (0:ℝ) T,E)) := additive_flow_second_derivative_exists b D D₂ hD hD₂ hcD₂ C L hDC hL hDb
    (fun s => w (projIcc 0 T hT s)) (w.continuous.comp continuous_projIcc) T hT
  choose X J hcX hcJ hLip hJ hX hJder hJb hKex using hex
  choose K hcK hK hKder using hKex
  let S : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E) :=
    fun p => ⟨fun t => X p.2 p.1 t.val,(hcX p.2 p.1).comp continuous_subtype_val⟩
  let JP : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E →L[ℝ] E) :=
    fun p => ⟨fun t => J p.2 p.1 t.val,(hcJ p.2 p.1).comp continuous_subtype_val⟩
  let KP : E × C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E →L[ℝ] E →L[ℝ] E) :=
    fun p => ⟨fun t => K p.2 p.1 t.val,(hcK p.2 p.1).comp continuous_subtype_val⟩
  have hp (r : ℝ) (hr : r∈Icc 0 T) : (projIcc 0 T hT r).val=r := by
    simp [projIcc,hr.1,hr.2]
  have hpt (t : Icc (0:ℝ) T) : projIcc 0 T hT t.val=t := Subtype.ext (hp t.val t.property)
  have hLb : LipschitzWith L b := by
    apply lipschitzWith_of_nnnorm_fderiv_le (fun z => (hD z).differentiableAt)
    intro z
    rw [(hD z).fderiv]
    exact_mod_cast hDb z
  obtain ⟨S₀,hS₀c,hS₀⟩ := additive_path_map_exists b L hLb T hT
  have hSeq (p : E × C(Icc (0:ℝ) T,E)) : S p=S₀ p := by
    apply ContinuousMap.ext
    intro t
    have hy s (hs : s∈Icc 0 T) : S₀ p (projIcc 0 T hT s)=p.1+
        (∫ r in 0..s,b (S₀ p (projIcc 0 T hT r)))+p.2 (projIcc 0 T hT s) := by
      have hh := hS₀ p (projIcc 0 T hT s)
      simpa only [hp s hs] using hh
    have hh := additive_path_unique b L hLb (X p.2 p.1)
      (fun r => S₀ p (projIcc 0 T hT r)) (fun r => p.2 (projIcc 0 T hT r))
      (hcX p.2 p.1) ((S₀ p).continuous.comp continuous_projIcc) p.1 T hT (hX p.2 p.1) hy t.val t.property
    simpa only [S,ContinuousMap.coe_mk,hpt] using hh
  have hSc : Continuous S := by
    convert hS₀c using 1
    funext p
    exact hSeq p
  have hJPc : Continuous JP := by
    apply first_variation_parameter_continuous T hT L (by exact_mod_cast hL) D hDC.continuous hDb S JP hSc
    intro p t
    apply ContinuousLinearMap.ext
    intro h
    change J p.2 p.1 t.val h=h+(∫ s in 0..t.val,D (S p (projIcc 0 T hT s))*JP p (projIcc 0 T hT s)) h
    rw [hJ p.2 p.1 t.val t.property h,ContinuousLinearMap.intervalIntegral_apply
      (φ := fun s => D (S p (projIcc 0 T hT s))*JP p (projIcc 0 T hT s))
      (((hDC.continuous.comp ((S p).continuous.comp continuous_projIcc)).mul
        ((JP p).continuous.comp continuous_projIcc)).intervalIntegrable 0 t.val)]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 t.val := by simpa only [uIcc_of_le t.property.1] using hr
    simp only [S,JP,ContinuousMap.coe_mk,hp r ⟨hr'.1,hr'.2.trans t.property.2⟩]
    rfl
  have hKPc : Continuous KP := by
    apply second_variation_parameter_continuous T hT L (by exact_mod_cast hL) D D₂ hDC.continuous hcD₂ hDb S JP KP hSc hJPc
    intro p t h k
    change K p.2 p.1 t.val h k=_
    rw [hK p.2 p.1 t.val t.property h k]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc 0 t.val := by simpa only [uIcc_of_le t.property.1] using hr
    simp only [S,JP,KP,ContinuousMap.coe_mk,hp r ⟨hr'.1,hr'.2.trans t.property.2⟩]
  refine ⟨S,JP,KP,hSc,hJPc,hKPc,?_,?_,?_,?_,?_⟩
  · intro p t
    rw [hSeq p]
    simpa only [hSeq] using hS₀ p t
  · intro x w t
    exact hJder w x t.val t.property
  · intro x w t
    exact hKder w x t.val t.property
  · intro p t
    exact hJb p.2 p.1 t.val t.property
  · intro p t
    have hh := second_variation_bound D C hDC (X p.2) (J p.2) (hcX p.2) (hcJ p.2) T
      (Real.exp (((L:ℝ)+1)*T)) (Real.exp (((L:ℝ)+1)*T)) L hT (Real.exp_pos _).le (Real.exp_pos _).le
      (by exact_mod_cast hL) hDb (hJb p.2) (hLip p.2) (hJ p.2) p.1 t.val t.property
      (K p.2 p.1 t.val) (hKder p.2 p.1 t.val t.property)
    convert hh using 1 <;> ring

end Asakura.Chapter8
