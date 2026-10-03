import Chapter7OrthogonalSquareSum
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory
namespace Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false

/-- Conditional centering suffices for orthogonality of successive blocks. -/
lemma conditional_centered_cross {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U V : Ω → ℝ)
    (hU : MemLp U 2 P) (hV : MemLp V 2 P)
    (F : MeasurableSpace Ω) (hle : F ≤ m)
    (hUm : StronglyMeasurable[F] U) (hVzero : P[V|F] =ᵐ[P] 0) :
    (∫ w,U w*V w ∂P)=0 := by
  letI : MeasurableSpace Ω := m
  letI : SigmaFinite (P.trim hle) := inferInstance
  have he := condExp_mul_of_stronglyMeasurable_left hUm (hU.integrable_mul hV)
    (hV.integrable (by norm_num))
  have hz : P[U*V|F] =ᵐ[P] 0 := by
    filter_upwards [he,hVzero] with w hw hv
    simpa only [Pi.mul_apply,hv,Pi.zero_apply,mul_zero] using hw
  have hi := integral_congr_ae hz
  rw [integral_condExp hle] at hi
  simpa only [Pi.mul_apply,Pi.zero_apply,integral_zero] using hi

end Asakura.Chapter7
