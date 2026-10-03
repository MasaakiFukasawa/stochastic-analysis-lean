import Chapter9EuclideanScore
import Chapter9OULaw

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter9
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Differentiate the actual log density for a deterministic initial point. -/
theorem radial_log_kernel_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c a v : ℝ) (hc : 0<c) (hv : 0<v) (x y : E) :
    HasFDerivAt (fun z => Real.log (radialKernel c a v x z))
      (innerSL ℝ ((-1/v) • (y-a • x))) y := by
  have hp : 0<radialKernel c a v x y := mul_pos hc (Real.exp_pos _)
  have hd := (radial_kernel_fderiv c a v hv.ne' x y).log hp.ne'
  convert hd using 1
  ext h
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp

theorem stationary_gaussian_gradient {d : ℕ} (y : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) =>
      Real.log (gaussianKernel 0 1 (fun _ => 0) (fun i => z i))) (innerSL ℝ (-y)) y := by
  have hd := radial_log_kernel_gradient
    (Real.exp (-(d:ℝ)/2*Real.log (2*Real.pi*1))) 0 1
    (Real.exp_pos _) (by norm_num) (0 : EuclideanSpace ℝ (Fin d)) y
  have he (z : EuclideanSpace ℝ (Fin d)) := gaussian_kernel_radial 0 1 (0 : EuclideanSpace ℝ (Fin d)) z
  simp only [PiLp.zero_apply] at he
  simp_rw [he]
  simpa using hd

/-- Constant paths solve the stationary probability-flow ODE in any
dimension and preserve every initial law, in particular the Gaussian law. -/
theorem constant_flow_stationary {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (P : Measure Ω) (X : Ω → E) :
    (∀ w t, HasDerivAt (fun _ : ℝ => X w) (-(X w)-(-(X w))) t) ∧
      (∀ t : ℝ, P.map (fun w => X w)=P.map X) := by
  constructor
  · intro w t
    simpa using hasDerivAt_const t (X w)
  · intro t
    rfl

/-- Under stationary Gaussian initialization, the OU displacement has
strictly positive second moment at every positive time in positive dimension. -/
theorem stationary_ou_displacement {d : ℕ} (t : ℝ) (ht : 0<t) :
    (∫ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d),
      ‖(Real.exp (-t)-1) • z.1+Real.sqrt (1-Real.exp (-2*t)) • z.2‖^2
      ∂(stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin d))))=
      2*(d:ℝ)*(1-Real.exp (-t)) := by
  rw [gaussian_affine_second_moment _ IsGaussian.memLp_two_id,
    standard_gaussian_second_moment]
  have hv : 0≤1-Real.exp (-2*t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [Real.sq_sqrt hv]
  have he : Real.exp (-2*t)=Real.exp (-t)^2 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem stationary_ou_displacement_positive {d : ℕ} (hd : 0<d) (t : ℝ) (ht : 0<t) :
    0<2*(d:ℝ)*(1-Real.exp (-t)) := by
  have hx : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  positivity
end Asakura.Chapter9
