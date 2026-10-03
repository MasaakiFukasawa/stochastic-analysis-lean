import Chapter9GaussianKernel

open Finset
open scoped BigOperators
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Direct time differentiation of the displayed OU Gaussian kernel. -/
theorem gaussian_kernel_time_derivative {d : ℕ} (x y : Fin d → ℝ)
    (t : ℝ) (ht : 0<t) :
    let a := Real.exp (-t)
    let v := 1-Real.exp (-2*t)
    HasDerivAt (fun s => gaussianKernel (Real.exp (-s)) (1-Real.exp (-2*s)) x y)
      (((a^2*((∑ i,(y i-a*x i)^2)/v^2-(d:ℝ)/v))-
      a*(∑ i,x i*(y i-a*x i))/v)*gaussianKernel a v x y) t := by
  dsimp only
  let a := Real.exp (-t)
  let v := 1-Real.exp (-2*t)
  have hv : 0<v := ou_variance_positive t ht
  obtain ⟨ha,hvD⟩ := ou_coefficients t
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((ha.mul_const (x i)).const_sub (y i)).pow 2))
  have hlog := (hvD.const_mul (2*Real.pi)).log (show 2*Real.pi*v≠0 by positivity)
  have hd := ((hlog.const_mul (-(d:ℝ)/2)).sub
    (hs.div (hvD.const_mul 2) (show 2*v≠0 by positivity))).exp
  convert hd using 1
  · funext s
    simp only [gaussianKernel,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,Finset.sum_apply]
  · simp only [gaussianKernel,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,Finset.sum_apply,Nat.reduceSub,pow_one,Nat.cast_ofNat]
    simp only [←show a=Real.exp (-t) from rfl,←show v=1-Real.exp (-2*t) from rfl]
    have hsum : (∑ i,2*(y i-a*x i)*(-(-a*x i)))=2*a*(∑ i,x i*(y i-a*x i)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    rw [hsum]
    field_simp [hv.ne',Real.pi_ne_zero]
    <;> ring
end Asakura.Chapter9
