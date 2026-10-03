import Chapter12AffineGaussianSmoothDensity
import Chapter12GaussianScaleKernelDerivative

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

noncomputable def gaussianScaleEquiv {d : ℕ} (s : ℝ) (hs : s≠0) :
    (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) where
  toFun z := s • z
  invFun z := s⁻¹ • z
  left_inv z := by simp [smul_smul,hs]
  right_inv z := by simp [smul_smul,hs]
  map_add' x y := smul_add s x y
  map_smul' a x := by simp [smul_smul,mul_comm]
  continuous_toFun := continuous_const_smul s
  continuous_invFun := continuous_const_smul s⁻¹

theorem gaussian_scale_affine_density {d : ℕ} (s : ℝ) (hs : 0<s)
    (k z : Fin d → ℝ) :
    affineGaussianDensity (gaussianScaleEquiv s hs.ne') (fun i => -s^2*k i/2) z=
      scaleGaussianKernel ((Real.sqrt (2*Real.pi))⁻¹^d) k z s := by
  have hlin : (gaussianScaleEquiv (d := d) s hs.ne').toLinearMap=s • LinearMap.id := by
    ext z i
    rfl
  have hdet : LinearMap.det (gaussianScaleEquiv (d := d) s hs.ne').toLinearMap=s^d := by
    rw [hlin,LinearMap.det_smul]
    simp
  have he : Real.exp (-(d:ℝ)*Real.log s)=(s^d)⁻¹ := by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hs]
  unfold affineGaussianDensity scaleGaussianKernel
  rw [hdet,abs_of_pos (inv_pos.mpr (pow_pos hs d))]
  have hi (i : Fin d) : (gaussianScaleEquiv s hs.ne').symm (z-(fun i => -s^2*k i/2)) i=
      z i/s+s*k i/2 := by
    change s⁻¹*(z i-(-s^2*k i/2))=_
    field_simp
    <;> ring
  simp only [hi]
  rw [sub_eq_add_neg,Real.exp_add,he]
  ring

theorem gaussian_scale_density_law {d : ℕ} (s : ℝ) (hs : 0<s) (k : Fin d → ℝ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (fun z i => s*z i-s^2*k i/2)=
      volume.withDensity (fun z => ENNReal.ofReal
        (scaleGaussianKernel ((Real.sqrt (2*Real.pi))⁻¹^d) k z s)) := by
  have hh := affine_gaussian_density_law (gaussianScaleEquiv (d := d) s hs.ne')
    (fun i => -s^2*k i/2)
  simp only [gaussian_scale_affine_density s hs] at hh
  convert hh using 1
  congr 1
  funext z i
  change s*z i-s^2*k i/2= -s^2*k i/2+s*z i
  ring

end Asakura.Chapter12
