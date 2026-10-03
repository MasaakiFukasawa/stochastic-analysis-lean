import Chapter12MixtureFourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

open MeasureTheory Real
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The inverse Gaussian damping integral is an explicit positive
Gaussian kernel. The normalization is left outside this identity. -/
theorem inverse_gaussian_kernel {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : ℝ) (hb : 0<b) (x : E) :
    (∫ ξ,Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*(Real.exp (-b*‖ξ‖^2):ℂ))=
      ((π/b)^(Module.finrank ℝ E/2:ℝ)*Real.exp (-‖x‖^2/(4*b)):ℝ) := by
  have he := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := E) (b := (b:ℂ)) (show 0<(b:ℂ).re from hb) (-Complex.I) x
  have hg (ξ : E) : Complex.exp (-Complex.I*(inner ℝ ξ x:ℂ))*(Real.exp (-b*‖ξ‖^2):ℂ)=
      Complex.exp (-(b:ℂ)*(‖ξ‖:ℂ)^2+(-Complex.I)*(inner ℝ x ξ:ℂ)) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    rw [real_inner_comm ξ x]
    push_cast
    ring
  simp_rw [hg]
  rw [he]
  rw [Complex.ofReal_mul,Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  simp [neg_sq,Complex.I_sq]

end Asakura.Chapter12
