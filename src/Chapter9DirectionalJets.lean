import Chapter9GaussianSmoothness
import Chapter9KernelTimeDerivative

open Set Finset
open scoped ContDiff
namespace Asakura.Chapter9
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [-instance] ContinuousMultilinearMap.seminormedAddCommGroup ContinuousMultilinearMap.seminormedAddCommGroup'

theorem first_jet_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (z h : E) (hf : ContDiffAt ℝ ∞ f z) :
    HasDerivAt (fun r : ℝ => f (z+r • h))
      (iteratedFDeriv ℝ 1 f z (fun _ => h)) 0 := by
  have hd := (hf.differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun r : ℝ => z+r • h) h 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add z
  simpa only [Function.comp_def,iteratedFDeriv_one_apply] using! hd.comp_hasDerivAt_of_eq 0 hl (by simp)

theorem second_jet_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (z h : E) (hf : ContDiffAt ℝ ∞ f z) :
    HasDerivAt (fun r : ℝ => iteratedFDeriv ℝ 1 f (z+r • h) (fun _ => h))
      (iteratedFDeriv ℝ 2 f z (fun _ => h)) 0 := by
  have hi : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) z :=
    (hf.iteratedFDeriv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have hd := (hi.continuousMultilinear_apply_const (fun _ : Fin 1 => h)).hasFDerivAt
  have hl : HasDerivAt (fun r : ℝ => z+r • h) h 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add z
  have hh := hd.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he := hi.iteratedFDeriv_succ_apply_left' (m := fun _ : Fin 2 => h)
  rw [he]
  simpa only [Function.comp_def,Fin.tail] using! hh

theorem ou_kernel_smooth_at {d : ℕ} (x : Fin d → ℝ) (t : ℝ) (ht : 0<t) (y : Fin d → ℝ) :
    ContDiffAt ℝ ∞ (fun q => Real.exp (ouExponent x q)) (t,y) :=
  (ou_exponent_smooth x).exp.contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)

theorem ou_kernel_spatial_first_jet {d : ℕ} (x y h : Fin d → ℝ) (t : ℝ) (ht : 0<t) :
    let a := Real.exp (-t)
    let v := 1-Real.exp (-2*t)
    iteratedFDeriv ℝ 1 (fun q => Real.exp (ouExponent x q)) (t,y)
      (fun _ => (0,h)) = (-(∑ i,(y i-a*x i)*h i)/v)*gaussianKernel a v x y := by
  dsimp only
  have hd := first_jet_line (fun q => Real.exp (ouExponent x q)) (t,y) (0,h)
    (ou_kernel_smooth_at x t ht y)
  have hg := gaussian_kernel_direction (Real.exp (-t)) (1-Real.exp (-2*t))
    (ou_variance_positive t ht).ne' x y h
  have he : (fun r : ℝ => Real.exp (ouExponent x ((t,y)+r • (0,h))))=
      (fun r => gaussianKernel (Real.exp (-t)) (1-Real.exp (-2*t)) x (fun i => y i+r*h i)) := by
    funext r
    simp [ouExponent,gaussianKernel,smul_eq_mul]
  rw [he] at hd
  exact hd.unique hg

theorem ou_kernel_spatial_second_jet {d : ℕ} (x y h : Fin d → ℝ) (t : ℝ) (ht : 0<t) :
    let a := Real.exp (-t)
    let v := 1-Real.exp (-2*t)
    iteratedFDeriv ℝ 2 (fun q => Real.exp (ouExponent x q)) (t,y)
      (fun _ => (0,h)) =
      (((∑ i,(y i-a*x i)*h i)^2/v^2-(∑ i,(h i)^2)/v)*gaussianKernel a v x y) := by
  dsimp only
  have hd := second_jet_line (fun q => Real.exp (ouExponent x q)) (t,y) (0,h)
    (ou_kernel_smooth_at x t ht y)
  have hg := gaussian_kernel_second_direction (Real.exp (-t)) (1-Real.exp (-2*t))
    (ou_variance_positive t ht).ne' x y h
  have he (r : ℝ) : (t,y)+r • (0,h)=(t,fun i => y i+r*h i) := by
    ext <;> simp [smul_eq_mul]
  simp_rw [he,ou_kernel_spatial_first_jet x _ h t ht] at hd
  exact hd.unique hg

theorem ou_kernel_time_jet {d : ℕ} (x y : Fin d → ℝ) (t : ℝ) (ht : 0<t) :
    let a := Real.exp (-t)
    let v := 1-Real.exp (-2*t)
    iteratedFDeriv ℝ 1 (fun q => Real.exp (ouExponent x q)) (t,y)
      (fun _ => (1,0)) =
      (a^2*((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)-
        a*(∑ i,x i*(y i-a*x i))/v)*gaussianKernel a v x y := by
  dsimp only
  have hd := first_jet_line (fun q => Real.exp (ouExponent x q)) (t,y) (1,0)
    (ou_kernel_smooth_at x t ht y)
  have hg := (gaussian_kernel_time_derivative x y t ht).comp_of_eq 0
    ((hasDerivAt_id (0:ℝ)).const_add t) (by simp)
  have he : (fun r : ℝ => Real.exp (ouExponent x ((t,y)+r • (1,0))))=
      (fun r => gaussianKernel (Real.exp (-(t+r))) (1-Real.exp (-2*(t+r))) x y) := by
    funext r
    simp [ouExponent,gaussianKernel,smul_eq_mul]
  rw [he] at hd
  simpa using hd.unique hg
end Asakura.Chapter9
