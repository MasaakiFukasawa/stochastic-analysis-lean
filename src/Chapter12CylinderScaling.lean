import Chapter12CylinderFromSmooth

open MeasureTheory
open scoped ContDiff
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable def scaleSmoothCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (a : ℝ) (c : SmoothCylinder H) : SmoothCylinder H :=
  smoothCylinderOfFunction c.direction (fun z => a • c.f z) (c.smooth.const_smul a) (by
    intro k
    obtain ⟨C,hC,b,hb⟩ := c.all_derivatives_growth k
    refine ⟨|a| *C,mul_nonneg (abs_nonneg _) hC,b,fun z => ?_⟩
    rw [iteratedFDeriv_const_smul_apply' (c.smooth.of_le (by simp)).contDiffAt,norm_smul]
    simpa only [Real.norm_eq_abs,mul_assoc] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg a))

theorem scaleSmoothCylinder_df {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : ℝ) (c : SmoothCylinder H) (z : Fin c.dim → ℝ) :
    (scaleSmoothCylinder a c).df z = a • c.df z := by
  exact ((c.derivative z).const_smul a).fderiv

theorem scaleSmoothCylinder_value {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (a : ℝ) (c : SmoothCylinder H) :
    (scaleSmoothCylinder a c).value P W = fun w => a • c.value P W w := rfl

theorem scaleSmoothCylinder_gradient {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (a : ℝ) (c : SmoothCylinder H) :
    (scaleSmoothCylinder a c).gradient P W = fun w => a • c.gradient P W w := by
  funext w
  unfold SmoothCylinder.gradient
  change (∑ j, (scaleSmoothCylinder a c).df (fun i => W (c.direction i) w) (Pi.single j 1) • c.direction j) = _
  simp only [scaleSmoothCylinder_df,ContinuousLinearMap.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]
  rfl

end Asakura.Chapter12
