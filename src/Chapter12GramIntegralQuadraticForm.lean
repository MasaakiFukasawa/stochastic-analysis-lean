import Chapter12MalliavinCovarianceLowerBound
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The integral of J A A* J* has the quadratic form used in the SDE proof. -/
theorem gram_integral_quadratic_form {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : ℝ → F →L[ℝ] E) (T : ℝ)
    (hi : IntegrableOn (fun s => (A s).comp (ContinuousLinearMap.adjoint (A s))) (Ioc (0:ℝ) T))
    (v : E) :
    inner ℝ v ((∫ s in Ioc (0:ℝ) T,(A s).comp (ContinuousLinearMap.adjoint (A s))) v)=
      ∫ s in Ioc (0:ℝ) T,‖ContinuousLinearMap.adjoint (A s) v‖^2 := by
  let L : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ v).comp (ContinuousLinearMap.apply ℝ E v)
  have he := L.integral_comp_comm hi
  change (∫ s in Ioc (0:ℝ) T,inner ℝ v ((A s) (ContinuousLinearMap.adjoint (A s) v)))=
    inner ℝ v ((∫ s in Ioc (0:ℝ) T,(A s).comp (ContinuousLinearMap.adjoint (A s))) v) at he
  rw [←he]
  apply integral_congr_ae
  apply ae_of_all
  intro s
  change inner ℝ v (A s (ContinuousLinearMap.adjoint (A s) v))=‖ContinuousLinearMap.adjoint (A s) v‖^2
  rw [←ContinuousLinearMap.adjoint_inner_left,real_inner_self_eq_norm_sq]

end Asakura.Chapter12
