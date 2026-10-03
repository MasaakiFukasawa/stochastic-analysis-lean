import Chapter12GaussianInverseSquare
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

noncomputable def squaredGaussianDensity (T : ℝ≥0) (x : ℝ) : ℝ :=
  if 0<x then (Real.sqrt (2*Real.pi*(T:ℝ)*x))⁻¹*Real.exp (-x/(2*(T:ℝ))) else 0

theorem squared_gaussian_density_nonneg (T : ℝ≥0) (x : ℝ) :
    0≤squaredGaussianDensity T x := by
  unfold squaredGaussianDensity
  split_ifs <;> positivity

theorem squared_gaussian_density_measurable (T : ℝ≥0) :
    Measurable (squaredGaussianDensity T) := by
  unfold squaredGaussianDensity
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

theorem square_image_positive : (fun x : ℝ => x^2) '' Ioi (0:ℝ)=Ioi (0:ℝ) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact sq_pos_of_pos (show 0<x from hx)
  · intro hy
    exact ⟨Real.sqrt y,Real.sqrt_pos.mpr hy,Real.sq_sqrt hy.le⟩

theorem square_injective_positive : InjOn (fun x : ℝ => x^2) (Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  change 0<x at hx
  change 0<y at hy
  change x^2=y^2 at hxy
  nlinarith

theorem squared_gaussian_jacobian (T : ℝ≥0) (hT : T≠0) (x : ℝ) (hx : 0<x) :
    |2*x| *squaredGaussianDensity T (x^2)=2*gaussianPDFReal 0 T x := by
  rw [squaredGaussianDensity,if_pos (sq_pos_of_pos hx)]
  rw [Real.sqrt_mul (show 0≤2*Real.pi*(T:ℝ) by positivity),Real.sqrt_sq hx.le]
  rw [abs_of_pos (mul_pos (by norm_num) hx)]
  unfold gaussianPDFReal
  simp only [sub_zero]
  rw [mul_inv_rev]
  field_simp
  <;> ring

theorem squared_gaussian_change_variables (T : ℝ≥0) (hT : T≠0) (f : ℝ → ℝ) :
    (∫ y in Ioi (0:ℝ),squaredGaussianDensity T y*f y)=
      ∫ x in Ioi (0:ℝ),2*gaussianPDFReal 0 T x*f (x^2) := by
  have hd (x : ℝ) (_ : x∈Ioi (0:ℝ)) : HasDerivWithinAt (fun x : ℝ => x^2) (2*x) (Ioi (0:ℝ)) x := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq,Pi.pow_apply] using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd square_injective_positive
    (fun y => squaredGaussianDensity T y*f y)
  rw [square_image_positive] at hh
  rw [hh]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change |2*x| *(squaredGaussianDensity T (x^2)*f (x^2))=_
  rw [←mul_assoc,squared_gaussian_jacobian T hT x hx]

end Asakura.Chapter12
