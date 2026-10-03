import Chapter8ContinuousVariationalDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Prod

open MeasureTheory Set
namespace Asakura.Chapter8
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

noncomputable def augmentedDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (p : E × (E →L[ℝ] E)) : (E × (E →L[ℝ] E)) →L[ℝ] E × (E →L[ℝ] E) :=
  ((D p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))).prod
    (((ContinuousLinearMap.compL ℝ E E E).flip p.2).comp
      ((D₂ p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)))+
    (ContinuousLinearMap.compL ℝ E E E (D p.1)).comp
      (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)))

 theorem augmented_derivative_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (p v : E × (E →L[ℝ] E)) :
    augmentedDerivative D D₂ p v=(D p.1 v.1,(D₂ p.1 v.1)*p.2+D p.1*v.2) := rfl

/-- Differentiate the augmented drift (b(x), b'(x)J). Its derivative
uses b'' and no higher derivative. -/
theorem augmented_drift_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E → E) (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ x,HasFDerivAt b (D x) x) (hD₂ : ∀ x,HasFDerivAt D (D₂ x) x)
    (p : E × (E →L[ℝ] E)) :
    HasFDerivAt (fun q : E × (E →L[ℝ] E) => (b q.1,D q.1*q.2)) (augmentedDerivative D D₂ p) p := by
  convert ((hD p.1).comp p hasFDerivAt_fst).prodMk
    (((hD₂ p.1).comp p hasFDerivAt_fst).mul' hasFDerivAt_snd) using 1
  · funext v
    simp only [Function.comp_def,Pi.mul_apply]
  · apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · change (D₂ p.1 v.1)*p.2+D p.1*v.2=D p.1*v.2+(D₂ p.1 v.1)*p.2
      exact add_comm _ _

theorem augmented_derivative_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E → E →L[ℝ] E) (D₂ : E → E →L[ℝ] E →L[ℝ] E)
    (hcD : Continuous D) (hcD₂ : Continuous D₂) : Continuous (augmentedDerivative D D₂) := by
  have hprod : Continuous (fun q :
      ((E × (E →L[ℝ] E)) →L[ℝ] E) × ((E × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E)) =>
      q.1.prod q.2) := (ContinuousLinearMap.prodₗᵢ ℝ).continuous
  have h1 : Continuous (fun p : E × (E →L[ℝ] E) =>
      (D p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E))) :=
    (hcD.comp continuous_fst).clm_comp continuous_const
  have h2 : Continuous (fun p : E × (E →L[ℝ] E) =>
      ((ContinuousLinearMap.compL ℝ E E E).flip p.2).comp
        ((D₂ p.1).comp (ContinuousLinearMap.fst ℝ E (E →L[ℝ] E)))+
      (ContinuousLinearMap.compL ℝ E E E (D p.1)).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] E))) :=
    ((continuous_const.clm_apply continuous_snd).clm_comp
      ((hcD₂.comp continuous_fst).clm_comp continuous_const)).add
      ((continuous_const.clm_apply (hcD.comp continuous_fst)).clm_comp continuous_const)
  exact hprod.comp (h1.prodMk h2)

end Asakura.Chapter8
