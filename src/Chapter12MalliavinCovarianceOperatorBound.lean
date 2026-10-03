import Chapter12GramIntegralQuadraticForm

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem malliavin_covariance_operator_lower_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : F →L[ℝ] E) (J : ℝ → E ≃L[ℝ] E) (K T ell : ℝ) (hT : 0≤T) (hell : 0≤ell)
    (hA : ∀ v : E,ell*‖v‖^2≤‖ContinuousLinearMap.adjoint A v‖^2)
    (hJ : ∀ s∈Ioc (0:ℝ) T,‖(J s).symm.toContinuousLinearMap‖≤Real.exp (K*T))
    (hi : IntegrableOn (fun s => ((J s).toContinuousLinearMap.comp A).comp
      (ContinuousLinearMap.adjoint ((J s).toContinuousLinearMap.comp A))) (Ioc (0:ℝ) T))
    (v : E) :
    ell*T*Real.exp (-2*K*T)*‖v‖^2≤
      inner ℝ v ((∫ s in Ioc (0:ℝ) T,((J s).toContinuousLinearMap.comp A).comp
        (ContinuousLinearMap.adjoint ((J s).toContinuousLinearMap.comp A))) v) := by
  let Q := fun s => (J s).toContinuousLinearMap.comp A
  let L : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)
  have hq (s : ℝ) : L ((Q s).comp (ContinuousLinearMap.adjoint (Q s)))=
      ‖ContinuousLinearMap.adjoint A (ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v)‖^2 := by
    change inner ℝ v (Q s (ContinuousLinearMap.adjoint (Q s) v))=_
    rw [←ContinuousLinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq]
    simp only [Q,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply]
  have hiq : IntegrableOn (fun s => ‖ContinuousLinearMap.adjoint A
      (ContinuousLinearMap.adjoint (J s).toContinuousLinearMap v)‖^2) (Ioc (0:ℝ) T) := by
    have hh := L.integrable_comp hi
    change IntegrableOn (fun s => L ((Q s).comp (ContinuousLinearMap.adjoint (Q s)))) (Ioc (0:ℝ) T) at hh
    simpa only [hq] using hh
  rw [gram_integral_quadratic_form (fun s => (J s).toContinuousLinearMap.comp A) T hi v]
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply]
  exact malliavin_covariance_integral_lower_bound A J K T ell hT hell hA hJ v hiq

end Asakura.Chapter12
