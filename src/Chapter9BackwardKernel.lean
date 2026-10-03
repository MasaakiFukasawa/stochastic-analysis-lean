import Chapter9KernelTimeDerivative

open Finset
namespace Asakura.Chapter9
set_option maxHeartbeats 1800000

theorem gaussian_initial_shift {d : ℕ} (a v r : ℝ) (x y h : Fin d → ℝ) :
    gaussianKernel a v (fun i => x i+r*h i) y=
      gaussianKernel a v x (fun i => y i+r*(-a*h i)) := by
  unfold gaussianKernel
  congr 3
  apply sum_congr rfl
  intro i _
  congr 1
  ring

theorem gaussian_kernel_initial_direction {d : ℕ} (a v : ℝ) (hv : v≠0)
    (x y h : Fin d → ℝ) :
    HasDerivAt (fun r => gaussianKernel a v (fun i => x i+r*h i) y)
      (a/v*(∑ i,(y i-a*x i)*h i)*gaussianKernel a v x y) 0 := by
  have hd := gaussian_kernel_direction a v hv x y (fun i => -a*h i)
  simp_rw [gaussian_initial_shift]
  convert hd using 1
  have he : (∑ i,(y i-a*x i)*(-a*h i))= -a*(∑ i,(y i-a*x i)*h i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem gaussian_kernel_initial_second_direction {d : ℕ} (a v : ℝ) (hv : v≠0)
    (x y h : Fin d → ℝ) :
    HasDerivAt (fun r =>
      (a/v*(∑ i,(y i-a*(x i+r*h i))*h i))*
        gaussianKernel a v (fun i => x i+r*h i) y)
      (a^2*((∑ i,(y i-a*x i)*h i)^2/v^2-(∑ i,h i^2)/v)*gaussianKernel a v x y) 0 := by
  have hd := gaussian_kernel_second_direction a v hv x y (fun i => -a*h i)
  convert hd using 1
  · funext r
    rw [gaussian_initial_shift]
    congr 1
    have he : (∑ i,(y i+r*(-a*h i)-a*x i)*(-a*h i))=
        -a*(∑ i,(y i-a*(x i+r*h i))*h i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [he]
    ring
  · have he : (∑ i,(y i-a*x i)*(-a*h i))= -a*(∑ i,(y i-a*x i)*h i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    have hs : (∑ i,(-a*h i)^2)=a^2*(∑ i,h i^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [he,hs]
    ring

/-- Sum the initial-coordinate second derivatives and subtract x times
the first derivatives. This is the actual time derivative already computed. -/
theorem gaussian_backward_generator {d : ℕ} (a v k : ℝ) (x y : Fin d → ℝ) :
    (∑ i,a^2*((y i-a*x i)^2/v^2-1/v)*k)-
      (∑ i,x i*(a/v*(y i-a*x i)*k))=
    (a^2*((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)-
      a*(∑ i,x i*(y i-a*x i))/v)*k := by
  have h1 : (∑ i,a^2*((y i-a*x i)^2/v^2-1/v)*k)=
      a^2*((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)*k := by
    calc
      _ = Finset.sum Finset.univ (fun i : Fin d => (a^2/v^2*k)*(y i-a*x i)^2-a^2/v*k) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [sum_sub_distrib,←mul_sum,sum_const]
        simp only [card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
  have h2 : (∑ i,x i*(a/v*(y i-a*x i)*k))=a/v*(∑ i,x i*(y i-a*x i))*k := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  rw [h1,h2]
  ring
end Asakura.Chapter9
