import Chapter12GaussianScaleScore

open Finset
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def scaleGaussianKernel {d : ℕ} (C : ℝ) (k z : Fin d → ℝ) (s : ℝ) : ℝ :=
  C*Real.exp (-(d:ℝ)*Real.log s-(∑ i,(z i/s+s*k i/2)^2)/2)

/-- At fixed observation z, the scale derivative has a quadratic score;
the cross terms cancel with the Black--Scholes mean adjustment. -/
theorem scale_gaussian_kernel_derivative {d : ℕ} (C s : ℝ) (hs : s≠0)
    (z k : Fin d → ℝ) :
    HasDerivAt (scaleGaussianKernel C k z)
      (scaleGaussianKernel C k z s*((∑ i,(z i)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4)) s := by
  let w : Fin d → ℝ := fun i => z i/s+s*k i/2
  have hz (i : Fin d) : s*w i-s^2*k i/2=z i := by
    dsimp [w]
    field_simp [hs]
    <;> ring
  have hd := gaussian_scale_density_score C s hs w k
  simp only [hz] at hd
  have he : ((∑ i,(w i)^2)-(d:ℝ))/s-(∑ i,k i*w i)=
      (∑ i,(z i)^2)/s^3-(d:ℝ)/s-s*(∑ i,(k i)^2)/4 := by
    have hi (i : Fin d) : (w i)^2/s-k i*w i=(z i)^2/s^3-s*(k i)^2/4 := by
      dsimp [w]
      field_simp [hs]
      <;> ring
    have hh := Finset.sum_congr rfl (fun i (_ : i∈Finset.univ) => hi i)
    simp only [Finset.sum_sub_distrib,div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum] at hh
    simp only [div_eq_mul_inv]
    nlinarith [hh]
  rw [he] at hd
  exact hd

end Asakura.Chapter12
