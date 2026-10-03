import Chapter12WienerFiniteFamilies

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem wiener_covariance_inner {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hlaw : ∀ h,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (u v : H) : covariance (W u : Ω → ℝ) (W v : Ω → ℝ) P=inner ℝ u v := by
  have hm (h : H) : (∫ w,W h w ∂P)=0 := by
    simpa only [integral_id_gaussianReal] using (hlaw h).integral_eq
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),hm,hm,mul_zero,sub_zero]
  have hh := W.inner_map_map u v
  rw [L2.inner_def] at hh
  simpa only [real_inner_comm,Real.inner_apply,Pi.mul_apply] using hh

end Asakura.Chapter12
