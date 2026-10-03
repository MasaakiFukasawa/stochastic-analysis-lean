import Chapter12SineCylinder

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
namespace Asakura.Chapter12
open Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

lemma L2_norm_sq_integral {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω) (u : Lp E 2 P) :
    ‖u‖^2 = ∫ w, ‖u w‖^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all P fun w => real_inner_self_eq_norm_sq (u w)

/-- The sine cylinders lie in the actual defining class of D; their
function norms vanish whereas their derivative norms stay bounded below. -/
theorem concrete_cylinder_derivative_not_bounded {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (h : H) (hh : ‖h‖ = 1) :
    ¬∃ C : ℝ, ∀ c : SmoothCylinder H,
      ‖c.gradientLp P W S hS hcore 2 (by simp)‖ ≤
        C * ‖c.valueLp P W S hS hcore 2 (by simp)‖ := by
  rintro ⟨C,hC⟩
  have hlaw : HasLaw (W h : Ω → ℝ) (gaussianReal 0 1) P := by
    have hv : (⟨‖h‖^2,sq_nonneg _⟩ : ℝ≥0) = 1 := by
      apply Subtype.ext
      change ‖h‖^2 = (1:ℝ)
      rw [hh]
      norm_num
    simpa only [hv] using (wiener_gaussian_law_from_dense_core P W S hS hcore h)
  apply gaussian_derivative_not_bounded
  refine ⟨C,fun a ha => ?_⟩
  let c := sineSmoothCylinder h a ha.ne'
  have hval : ‖c.valueLp P W S hS hcore 2 (by simp)‖^2 =
      ∫ z, (Real.sin (a*z)/a)^2 ∂gaussianReal 0 1 := by
    rw [L2_norm_sq_integral]
    calc
      _ = ∫ w, (Real.sin (a*W h w)/a)^2 ∂P := by
        apply integral_congr_ae
        filter_upwards [(c.value_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hw
        dsimp only [SmoothCylinder.valueLp]
        rw [hw,Real.norm_eq_abs,sq_abs]
        rfl
      _ = _ := hlaw.integral_comp (f := fun z : ℝ => (Real.sin (a*z)/a)^2) (by fun_prop)
  have hgrad : ‖c.gradientLp P W S hS hcore 2 (by simp)‖^2 =
      ∫ z, (Real.cos (a*z))^2 ∂gaussianReal 0 1 := by
    rw [L2_norm_sq_integral]
    calc
      _ = ∫ w, (Real.cos (a*W h w))^2 ∂P := by
        apply integral_congr_ae
        filter_upwards [(c.gradient_memLp P W S hS hcore 2 (by simp)).coeFn_toLp] with w hw
        dsimp only [SmoothCylinder.gradientLp]
        rw [hw]
        change ‖(sineSmoothCylinder h a ha.ne').gradient P W w‖^2 = _
        rw [sine_cylinder_gradient,norm_smul,hh,mul_one,Real.norm_eq_abs,sq_abs]
      _ = _ := hlaw.integral_comp (f := fun z : ℝ => (Real.cos (a*z))^2) (by fun_prop)
  rw [← hgrad,← hval,← mul_pow]
  have hc := hC c
  exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hc) |>.mpr hc

end Asakura.Chapter12
