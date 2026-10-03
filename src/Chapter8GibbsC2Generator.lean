import Chapter8GibbsCoordinateGenerator

open MeasureTheory
open scoped BigOperators
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The integrated Gibbs generator vanishes for the actual first and
second derivatives of a C2 function with bounded derivatives. -/
theorem gibbs_C2_generator_zero {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [Fintype ι]
    (U : E → ℝ) (DU : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hU : ∀ x, HasFDerivAt U (DU x) x) (hDU : Continuous DU)
    (hi : Integrable (fun x : E => (1+‖x‖^2)*Real.exp (-β*U x)))
    (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (e : ι → E) (he : ∀ i, ‖e i‖ ≤ 1) (M : ι → ι → ℝ)
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ A)
    (hd : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B)
    (hgrad : ∀ i x, |DU x (e i)| ≤ C*(1+‖x‖)) :
    (∫ x : E, Real.exp (-β*U x)*
      (∑ i, ∑ j, M i j*(-DU x (e i)*fderiv ℝ f x (e j)+
        β⁻¹*fderiv ℝ (fderiv ℝ f) x (e i) (e j)))) = 0 := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 1)).mp hf |>.2.2
  let ev (j : ι) := ContinuousLinearMap.apply ℝ ℝ (e j)
  let DF (j : ι) (x : E) := (ev j).comp (fderiv ℝ (fderiv ℝ f) x)
  have hDF j : Continuous (DF j) :=
    continuous_const.clm_comp (hf1.continuous_fderiv (by norm_num))
  have hF j x : HasFDerivAt (fun y => fderiv ℝ f y (e j)) (DF j x) x := by
    exact (ev j).hasFDerivAt.comp x ((hf1.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  have hfb j x : |fderiv ℝ f x (e j)| ≤ A := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ f x).le_opNorm (e j)).trans
      ((mul_le_mul (hb x) (he j) (norm_nonneg _) hA).trans_eq (mul_one A))
  have hdb i j x : |DF j x (e i)| ≤ B := by
    change |fderiv ℝ (fderiv ℝ f) x (e i) (e j)| ≤ B
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) x (e i)‖ * ‖e j‖ := (fderiv ℝ (fderiv ℝ f) x (e i)).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖e i‖) * ‖e j‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) x).le_opNorm _) (norm_nonneg _)
      _ ≤ (B*1)*1 := mul_le_mul (mul_le_mul (hd x) (he i) (norm_nonneg _) hB)
        (he j) (norm_nonneg _) (by positivity)
      _ = B := by ring
  exact gibbs_coordinate_generator_zero U DU β hβ hU hDU hi
    (fun j x => fderiv ℝ f x (e j)) DF hDF hF e M A B C hA hB hC hfb hdb hgrad

end Asakura.Chapter8
