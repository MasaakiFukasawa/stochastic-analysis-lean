import Chapter9BackwardKernel
import Chapter9SliceDerivatives
import Chapter9ReverseIntegralGenerator

open Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem gaussian_initial_smooth {d : ℕ} (a v : ℝ) (x : Fin d → ℝ) :
    ContDiff ℝ ∞ (fun y => gaussianKernel a v y x) := by
  unfold gaussianKernel
  fun_prop

theorem gaussian_actual_initial_direction {d : ℕ} (a v : ℝ) (hv : v≠0) (y x h : Fin d → ℝ) :
    directional (fun z => gaussianKernel a v z x) h y=
      (a/v*(∑ i,(x i-a*y i)*h i)*gaussianKernel a v y x) := by
  have hd := first_jet_line (fun z => gaussianKernel a v z x) y h (gaussian_initial_smooth a v x).contDiffAt
  have he := gaussian_kernel_initial_direction a v hv y x h
  simpa only [iteratedFDeriv_one_apply,directional,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hd.unique he

theorem gaussian_actual_initial_second_direction {d : ℕ} (a v : ℝ) (hv : v≠0)
    (y x h : Fin d → ℝ) :
    directional (directional (fun z => gaussianKernel a v z x) h) h y=
      a^2*((∑ i,(x i-a*y i)*h i)^2/v^2-(∑ i,h i^2)/v)*gaussianKernel a v y x := by
  have hd := first_jet_line (directional (fun z => gaussianKernel a v z x) h) y h
    (directional_smooth _ (gaussian_initial_smooth a v x) h).contDiffAt
  have he := gaussian_kernel_initial_second_direction a v hv y x h
  simp_rw [gaussian_actual_initial_direction a v hv] at hd
  simpa only [iteratedFDeriv_one_apply,directional,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using hd.unique he

theorem ou_kernel_actual_backward_derivative {d : ℕ} (t : ℝ) (ht : 0<t) (y x : Fin d → ℝ) :
    HasDerivAt (fun s => gaussianKernel (Real.exp (-s)) (1-Real.exp (-2*s)) y x)
      (ouBackward (fun z => gaussianKernel (Real.exp (-t)) (1-Real.exp (-2*t)) z x) y) t := by
  have hd := gaussian_kernel_time_derivative y x t ht
  convert hd using 1
  unfold ouBackward
  simp_rw [gaussian_actual_initial_second_direction _ _ (ou_variance_positive t ht).ne',
    gaussian_actual_initial_direction _ _ (ou_variance_positive t ht).ne']
  simp only [Pi.single_apply,mul_ite,ite_pow,one_pow,mul_one,mul_zero,zero_pow (by decide : 2≠0),sum_ite_eq',mem_univ,ite_true]
  rw [sum_sub_distrib]
  exact gaussian_backward_generator _ _ _ y x
end Asakura.Chapter9
