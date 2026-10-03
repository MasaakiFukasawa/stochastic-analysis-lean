import Chapter8LinearPullbackDerivatives

open scoped NNReal
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

theorem linear_coordinate_derivative_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E →L[ℝ] F)
    (f : F → ℝ) (hf : ContDiff ℝ 3 f)
    (A₂ A₃ : ℝ≥0)
    (h₂ : ∀ x,‖fderiv ℝ (fderiv ℝ f) x‖≤(A₂:ℝ))
    (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖≤(A₃:ℝ)) :
    ∃ B₂ B₃ : ℝ≥0,
      (∀ x,‖fderiv ℝ (fderiv ℝ (fun y => f (Q y))) x‖≤(B₂:ℝ)) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f (Q y)))) x‖≤(B₃:ℝ)) := by
  let A₁ := derivativeTransform Q (ContinuousLinearMap.id ℝ ℝ)
  let A₂' := derivativeTransform Q A₁
  let A₃' := derivativeTransform Q A₂'
  have hf1 : ContDiff ℝ 2 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 2)).mp hf |>.2.2
  have hf2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := (contDiff_succ_iff_fderiv (n := 1)).mp hf1 |>.2.2
  have h1 : fderiv ℝ (fun y => f (Q y))=fun x => A₁ (fderiv ℝ f (Q x)) := by
    funext x
    exact (derivative_transform_chain Q (ContinuousLinearMap.id ℝ ℝ) f x _
      ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt)).fderiv
  have h2 : fderiv ℝ (fderiv ℝ (fun y => f (Q y)))=fun x => A₂' (fderiv ℝ (fderiv ℝ f) (Q x)) := by
    rw [h1]
    funext x
    exact (derivative_transform_chain Q A₁ (fderiv ℝ f) x _
      ((hf1.differentiable (by norm_num)).differentiableAt.hasFDerivAt)).fderiv
  have h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f (Q y))))=
      fun x => A₃' (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (Q x)) := by
    rw [h2]
    funext x
    exact (derivative_transform_chain Q A₂' (fderiv ℝ (fderiv ℝ f)) x _
      ((hf2.differentiable (by norm_num)).differentiableAt.hasFDerivAt)).fderiv
  refine ⟨⟨‖A₂'‖*(A₂:ℝ),by positivity⟩,⟨‖A₃'‖*(A₃:ℝ),by positivity⟩,?_,?_⟩
  · intro x
    rw [h2]
    exact (A₂'.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h₂ _) (norm_nonneg _))
  · intro x
    rw [h3]
    exact (A₃'.le_opNorm _).trans (mul_le_mul_of_nonneg_left (h₃ _) (norm_nonneg _))


end Asakura.Chapter8
