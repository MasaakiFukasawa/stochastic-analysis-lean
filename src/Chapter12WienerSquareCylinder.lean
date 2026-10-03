import Chapter12CylinderProduct
import Chapter12LinearCylinder

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def squareWienerCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (h : H) : SmoothCylinder H :=
  mulSmoothCylinder (linearSmoothCylinder h) (linearSmoothCylinder h)

theorem square_wiener_cylinder_value {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (h : H) :
    (squareWienerCylinder h).value P W=fun w => (W h w)^2 := by
  rw [squareWienerCylinder,mulSmoothCylinder_value,linear_cylinder_value]
  funext w
  exact (pow_two _).symm

theorem square_wiener_cylinder_gradient {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (h : H) :
    (squareWienerCylinder h).gradient P W=fun w => (2*W h w) • h := by
  rw [squareWienerCylinder,mulSmoothCylinder_gradient,linear_cylinder_value,linear_cylinder_gradient]
  funext w
  dsimp only
  rw [←add_smul,two_mul]

theorem square_wiener_cylinder_covariance {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (h : H) (w : Ω) :
    inner ℝ ((squareWienerCylinder h).gradient P W w)
      ((squareWienerCylinder h).gradient P W w)=4*‖h‖^2*(W h w)^2 := by
  rw [square_wiener_cylinder_gradient]
  simp only [inner_smul_left,inner_smul_right,RCLike.conj_to_real,real_inner_self_eq_norm_sq]
  ring

end Asakura.Chapter12
