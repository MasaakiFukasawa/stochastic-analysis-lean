import Chapter9GaussianKernel
import Chapter9KernelDensity

open Finset
namespace Asakura.Chapter9
set_option maxHeartbeats 700000

/-- As a function of its starting point, the OU kernel is a Gaussian
density times the inverse contraction Jacobian. -/
theorem reverse_kernel_gaussian_identity {d : ℕ} (a v : ℝ) (ha : 0<a) (hv : 0<v)
    (x y : Fin d → ℝ) :
    gaussianKernel a v y x=Real.exp (-(d:ℝ)*Real.log a)*
      gaussianKernel a⁻¹ (v/a^2) x y := by
  have hl : Real.log (2*Real.pi*(v/a^2))=
      Real.log (2*Real.pi*v)-2*Real.log a := by
    rw [←mul_div_assoc,Real.log_div (by positivity) (by positivity),Real.log_pow]
    norm_num
  have hs : (∑ i,(y i-a⁻¹*x i)^2)/(2*(v/a^2))=
      (∑ i,(x i-a*y i)^2)/(2*v) := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    <;> ring
  unfold gaussianKernel
  rw [hl,hs,←Real.exp_add]
  congr 1
  ring

 theorem ou_reverse_kernel_gaussian_identity {d : ℕ} (h : ℝ) (hh : 0<h)
    (x y : Fin d → ℝ) :
    gaussianKernel (Real.exp (-h)) (1-Real.exp (-2*h)) y x=
      Real.exp ((d:ℝ)*h)*gaussianKernel (Real.exp h)
        ((1-Real.exp (-2*h))/(Real.exp (-h))^2) x y := by
  have he := reverse_kernel_gaussian_identity (Real.exp (-h)) (1-Real.exp (-2*h))
    (Real.exp_pos _) (ou_variance_positive h hh) x y
  rw [Real.log_exp] at he
  rw [show -(d:ℝ)*(-h)=(d:ℝ)*h by ring,
    show (Real.exp (-h))⁻¹=Real.exp h by rw [Real.exp_neg,inv_inv]] at he
  exact he
end Asakura.Chapter9
