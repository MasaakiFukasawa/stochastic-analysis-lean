import FullAuditGaussianIBP
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset
open scoped BigOperators
namespace Asakura.Chapter9
set_option maxHeartbeats 1200000

/-- Gaussian transition density, written as one exponential. -/
noncomputable def gaussianKernel {d : ℕ} (a v : ℝ) (x y : Fin d → ℝ) : ℝ :=
  Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*v)-(∑ i,(y i-a*x i)^2)/(2*v))

theorem gaussian_kernel_positive {d : ℕ} (a v : ℝ) (x y : Fin d → ℝ) :
    0<gaussianKernel a v x y := Real.exp_pos _

/-- Directional spatial derivative of the actual kernel, in any dimension. -/
theorem gaussian_kernel_direction {d : ℕ} (a v : ℝ) (hv : v≠0)
    (x y h : Fin d → ℝ) :
    HasDerivAt (fun r : ℝ => gaussianKernel a v x (fun i => y i+r*h i))
      ((-(∑ i,(y i-a*x i)*h i)/v)*gaussianKernel a v x y) 0 := by
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    ((((hasDerivAt_id (0:ℝ)).mul_const (h i)).const_add (y i)).sub_const (a*x i)).pow 2)
  have hd := ((hasDerivAt_const (0:ℝ) (-(d:ℝ)/2*Real.log (2*Real.pi*v))).sub (hs.div_const (2*v))).exp
  convert hd using 1
  · funext r
    simp only [gaussianKernel,Pi.sub_apply,Pi.pow_apply,Pi.mul_apply,Pi.neg_apply,Finset.sum_apply,id_eq]
  · simp only [id_eq,Pi.sub_apply,Pi.pow_apply,Finset.sum_apply,one_mul,zero_mul,add_zero,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one,sub_zero,zero_sub,gaussianKernel]
    rw [show (∑ i,2*(y i-a*x i)*h i)=2*(∑ i,(y i-a*x i)*h i) by simp only [mul_sum]; apply sum_congr rfl; intro i _; ring]
    field_simp
    <;> ring

/-- The second directional derivative is the square-score term minus the
constant covariance term, as used in the score Hessian calculation. -/
theorem gaussian_kernel_second_direction {d : ℕ} (a v : ℝ) (hv : v≠0)
    (x y h : Fin d → ℝ) :
    HasDerivAt (fun r : ℝ =>
      (-(∑ i,(y i+r*h i-a*x i)*h i)/v)*gaussianKernel a v x (fun i => y i+r*h i))
      ((((∑ i,(y i-a*x i)*h i)^2/v^2)-(∑ i,(h i)^2)/v)*gaussianKernel a v x y) 0 := by
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((((hasDerivAt_id (0:ℝ)).mul_const (h i)).const_add (y i)).sub_const (a*x i)).mul_const (h i)))
  have hd := (hs.neg.div_const v).mul (gaussian_kernel_direction a v hv x y h)
  convert hd using 1
  · funext r
    simp only [gaussianKernel,Pi.sub_apply,Pi.pow_apply,Pi.mul_apply,Pi.neg_apply,Finset.sum_apply,id_eq]
  · simp only [id_eq,zero_mul,add_zero,one_mul,mul_one,Pi.neg_apply,Finset.sum_apply]
    rw [show (∑ i,h i*h i)=∑ i,(h i)^2 by apply sum_congr rfl; intro i _; ring]
    ring

/-- OU coefficients have exactly the derivatives used in the text. -/
theorem ou_coefficients (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t ∧
    HasDerivAt (fun s => 1-Real.exp (-2*s)) (2*(Real.exp (-t))^2) t := by
  constructor
  · convert ((hasDerivAt_id t).neg.exp) using 1 <;> simp
  · have hd := (((hasDerivAt_id t).const_mul (-2)).exp).const_sub 1
    convert hd using 1
    · rfl
    · simp only [id_eq,mul_one,pow_two,←Real.exp_add]
      rw [show -t + -t = -2*t by ring]
      ring

theorem ou_variance_positive (t : ℝ) (ht : 0<t) : 0<1-Real.exp (-2*t) := by
  have h := Real.exp_lt_one_iff.mpr (show -2*t<0 by linarith)
  linarith

/-- The forward and backward generators agree with the time derivative
once the explicitly differentiated Gaussian factors are substituted. -/
theorem gaussian_forward_backward_algebra {d : ℕ} (a v k : ℝ) (hv : v≠0)
    (hav : a^2+v=1) (x y : Fin d → ℝ) :
    ((a^2*((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v))-
      a*(∑ i,x i*(y i-a*x i))/v)*k =
    (((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v)+(d:ℝ)-
      (∑ i,y i*(y i-a*x i))/v)*k := by
  have hs : (∑ i,y i*(y i-a*x i))=(∑ i,(y i-a*x i)^2)+a*(∑ i,x i*(y i-a*x i)) := by
    simp only [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [hs,show a^2=1-v by linarith]
  field_simp
  <;> ring
end Asakura.Chapter9
