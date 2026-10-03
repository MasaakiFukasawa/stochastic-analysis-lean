import Chapter12SquaredGaussianKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem squared_gaussian_density_integrable (T : ℝ≥0) (hT : T≠0) :
    Integrable (squaredGaussianDensity T) volume := by
  have hd (x : ℝ) (_ : x∈Ioi (0:ℝ)) : HasDerivWithinAt (fun x : ℝ => x^2) (2*x) (Ioi (0:ℝ)) x := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq,Pi.pow_apply] using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd
    square_injective_positive (squaredGaussianDensity T)
  rw [square_image_positive] at hi
  have hh : IntegrableOn (fun x : ℝ => |2*x| • squaredGaussianDensity T (x^2)) (Ioi (0:ℝ)) := by
    apply ((integrable_gaussianPDFReal 0 T).const_mul 2).integrableOn.congr_fun _ measurableSet_Ioi
    intro x hx
    exact (squared_gaussian_jacobian T hT x hx).symm
  have hj := (hi.mpr hh).integrable_indicator measurableSet_Ioi
  have he : (Ioi (0:ℝ)).indicator (squaredGaussianDensity T)=squaredGaussianDensity T := by
    funext x
    by_cases hx : 0<x
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem (show x∉Ioi (0:ℝ) from hx),squaredGaussianDensity,if_neg hx]
  rw [he] at hj
  exact hj

theorem even_integral_positive_half (f : ℝ → ℝ) (hi : Integrable f volume)
    (he : ∀ x,f (-x)=f x) : (∫ x,f x)=2*(∫ x in Ioi (0:ℝ),f x) := by
  have hn := integral_comp_neg_Ioi 0 f
  simp only [neg_zero,he] at hn
  have hh := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hi
  rw [compl_Ioi,←hn] at hh
  linarith

theorem gaussian_pdf_even (T : ℝ≥0) (x : ℝ) : gaussianPDFReal 0 T (-x)=gaussianPDFReal 0 T x := by
  simp only [gaussianPDFReal,sub_zero,neg_sq]

end Asakura.Chapter12
