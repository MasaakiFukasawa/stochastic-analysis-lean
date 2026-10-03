import Chapter12SineDerivativeBounds

open MeasureTheory Set
open scoped ContDiff ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

noncomputable def sineSmoothCylinder {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (h : H) (a : ℝ) (ha : a ≠ 0) : SmoothCylinder H where
  dim := 1
  direction := fun _ => h
  f := fun z => Real.sin (a*z 0)/a
  df := fun z => Real.cos (a*z 0) • ContinuousLinearMap.proj 0
  smooth := (contDiff_const.mul (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).contDiff).sin.div_const a
  derivative := fun z => by
    have hd := (sine_scaled_derivative a (z 0) ha).hasFDerivAt.comp z
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
    have he : (ContinuousLinearMap.toSpanSingleton ℝ (Real.cos (a*z 0))).comp
        (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) =
        Real.cos (a*z 0) • ContinuousLinearMap.proj 0 := by
      ext v
      simp [smul_eq_mul,mul_comm]
    rw [he] at hd
    exact hd
  growth := by
    refine ⟨|a|⁻¹,by positivity,0,fun z => ?_⟩
    simp only [pow_zero,mul_one,abs_div]
    exact (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq (one_div _)
  derivative_measurable := fun j => by fun_prop
  derivative_growth := fun j => by
    refine ⟨1,zero_le_one,0,fun z => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    simp only [hj,ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,Pi.single_eq_same,
      smul_eq_mul,mul_one,pow_zero]
    exact Real.abs_cos_le_one _
  all_derivatives_growth := fun k => by
    have h := scaled_sine_linear_all_derivatives_growth
      (a • (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)) a⁻¹ k
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
      div_eq_mul_inv,mul_comm] using h

theorem sine_cylinder_gradient {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (h : H) (a : ℝ) (ha : a ≠ 0) :
    (sineSmoothCylinder h a ha).gradient P W = fun w => Real.cos (a*W h w) • h := by
  funext w
  simp [SmoothCylinder.gradient,sineSmoothCylinder,Fin.sum_univ_one]

end Asakura.Chapter12
