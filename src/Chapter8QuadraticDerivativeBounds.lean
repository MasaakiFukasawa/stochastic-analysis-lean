import Chapter8PotentialDriftRegularity
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

open scoped NNReal
namespace Asakura.Chapter8
attribute [local instance] nestedOpNormed nestedOpSpace nestedBiNormed nestedBiSpace
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

theorem quadratic_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) :
    fderiv ℝ (fun x => B x x)=fun x => (B+B.flip) x := by
  funext x
  apply HasFDerivAt.fderiv
  have hh := B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
  have he : B.precompR E x (ContinuousLinearMap.id ℝ E)+B.precompL E (ContinuousLinearMap.id ℝ E) x=(B+B.flip) x := by
    apply ContinuousLinearMap.ext
    intro y
    rfl
  simp only [id_eq] at hh
  rw [he] at hh
  exact hh

/-- Adding kinetic energy preserves bounded second and third derivatives;
the third derivative of the quadratic term is exactly zero. -/
theorem add_quadratic_derivative_bounds {d : ℕ}
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 3 f)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ)
    (A₂ A₃ : ℝ≥0)
    (h₂ : ∀ x,‖fderiv ℝ (fderiv ℝ f) x‖≤(A₂:ℝ))
    (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖≤(A₃:ℝ)) :
    ContDiff ℝ 3 (fun x => f x+B x x) ∧ ∃ C₂ C₃ : ℝ≥0,
      (∀ x,‖fderiv ℝ (fderiv ℝ (fun y => f y+B y y)) x‖≤(C₂:ℝ)) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f y+B y y))) x‖≤(C₃:ℝ)) := by
  have hq : ContDiff ℝ 3 (fun x => B x x) := B.contDiff.clm_apply contDiff_id
  have hf1 : ContDiff ℝ 2 (fderiv ℝ f) := (contDiff_succ_iff_fderiv (n := 2)).mp hf |>.2.2
  have hf2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := (contDiff_succ_iff_fderiv (n := 1)).mp hf1 |>.2.2
  have h1 : fderiv ℝ (fun x => f x+B x x)=fun x => fderiv ℝ f x+(B+B.flip) x := by
    funext x
    change fderiv ℝ (f+(fun y => B y y)) x=_
    rw [fderiv_add (hf.differentiable (by norm_num)).differentiableAt (hq.differentiable (by norm_num)).differentiableAt,
      quadratic_fderiv]
  have h2 : fderiv ℝ (fderiv ℝ (fun x => f x+B x x))=fun x => fderiv ℝ (fderiv ℝ f) x+(B+B.flip) := by
    rw [h1]
    funext x
    change fderiv ℝ (fderiv ℝ f + fun y => (B+B.flip) y) x=_
    rw [fderiv_add (hf1.differentiable (by norm_num)).differentiableAt (B+B.flip).differentiableAt]
    simp only [ContinuousLinearMap.fderiv]
  have h3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => f x+B x x)))=fderiv ℝ (fderiv ℝ (fderiv ℝ f)) := by
    rw [h2]
    funext x
    exact fderiv_add_const _
  refine ⟨hf.add hq,⟨(A₂:ℝ)+‖B+B.flip‖,by positivity⟩,A₃,?_,?_⟩
  · intro x
    rw [h2]
    exact (norm_add_le _ _).trans (add_le_add (h₂ x) le_rfl)
  · intro x
    rw [h3]
    exact h₃ x

end Asakura.Chapter8
