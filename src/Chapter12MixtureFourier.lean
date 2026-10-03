import Chapter12GaussianDampedFourierLimit
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- Fubini identifies the inverse Fourier integral of a damped
characteristic function with the mixture of the inverse damping kernel. -/
theorem mixture_inverse_fourier {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [SFinite ν]
    (q : E → ℂ) (hq : Integrable q ν) (x : E) :
    (∫ y, (∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ (x-y):ℂ))*q ξ ∂ν) ∂μ)=
    ∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*
      (∫ y,Complex.exp (Complex.I*(inner ℝ ξ y:ℂ)) ∂μ)*q ξ ∂ν := by
  have hm : AEStronglyMeasurable (fun z : E × E =>
      Complex.exp (-Complex.I*(inner ℝ z.2 (x-z.1):ℂ))*q z.2) (μ.prod ν) :=
    (show Continuous (fun z : E × E =>
      Complex.exp (-Complex.I*(inner ℝ z.2 (x-z.1):ℂ))) by fun_prop).aestronglyMeasurable.mul
      (hq.aestronglyMeasurable.comp_snd)
  have hi : Integrable (fun z : E × E =>
      Complex.exp (-Complex.I*(inner ℝ z.2 (x-z.1):ℂ))*q z.2) (μ.prod ν) := by
    apply (hq.norm.comp_snd μ).mono' hm
    apply ae_of_all
    intro z
    simp [norm_mul,Complex.norm_exp]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  have he (y : E) : Complex.exp (-Complex.I*(inner ℝ ξ (x-y):ℂ))*q ξ=
      Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*
        Complex.exp (Complex.I*(inner ℝ ξ y:ℂ))*q ξ := by
    rw [← Complex.exp_add]
    congr 2
    simp only [inner_sub_right,Complex.ofReal_sub]
    ring
  simp_rw [he]
  rw [integral_mul_const,integral_const_mul]

end Asakura.Chapter12
