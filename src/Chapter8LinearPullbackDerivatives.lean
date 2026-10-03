import Chapter8PotentialDriftRegularity

open scoped NNReal
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
noncomputable section

def derivativeTransform {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Q : E →L[ℝ] F) (A : G →L[ℝ] H) : (F →L[ℝ] G) →L[ℝ] E →L[ℝ] H :=
  ((ContinuousLinearMap.compL ℝ E F H).flip Q).comp ((ContinuousLinearMap.compL ℝ F G H) A)

theorem derivative_transform_chain {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Q : E →L[ℝ] F) (A : G →L[ℝ] H) (f : F → G)
    (x : E) (D : F →L[ℝ] G) (hf : HasFDerivAt f D (Q x)) :
    HasFDerivAt (fun y => A (f (Q y))) (derivativeTransform Q A D) x := by
  exact A.hasFDerivAt.comp x (hf.comp x Q.hasFDerivAt)

/-- Bounded second and third derivatives are preserved by a linear change
of input variables, without requiring a bounded first derivative. -/
theorem linear_pullback_derivative_bounds {a b : ℕ}
    (Q : (Fin a → ℝ) →L[ℝ] (Fin b → ℝ))
    (f : (Fin b → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
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

end
end Asakura.Chapter8
