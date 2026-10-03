import Chapter12HigherChainLinearSplit

open scoped ContDiff BigOperators
namespace Asakura.Chapter12
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

theorem identity_higher_derivative_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (x : E) :
    iteratedFDeriv ℝ (n+2) (id : E → E) x=0 := by
  apply norm_eq_zero.mp
  rw [←norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ (id : E → E) = fun _ : E => ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  rw [he]
  simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]

theorem inverse_higher_derivative_formula {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (g : F → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f)
    (n : ℕ) (x : F) (v : Fin (n+2) → F) :
    iteratedFDeriv ℝ (n+2) g x v =
      -(fderiv ℝ g x) (higherChainRemainder g f (n+2) x v) := by
  have hfg : f ∘ g=id := funext hr
  have hgf : g ∘ f=id := funext hl
  have hsplit := higher_chain_linear_split g f hg hf (n+1) x v
  rw [hfg,identity_higher_derivative_zero] at hsplit
  have hder := ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=f (g x))).comp
    (g x) ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=g x))
  rw [hgf] at hder
  have he := hder.unique (hasFDerivAt_id (g x))
  rw [hr x] at he
  have hz := congrArg (fderiv ℝ g x) hsplit
  simp only [ContinuousMultilinearMap.zero_apply,map_zero,map_add] at hz
  have hi := congrArg (fun L : E →L[ℝ] E => L (iteratedFDeriv ℝ (n+2) g x v)) he
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi
  rw [hi] at hz
  exact eq_neg_of_add_eq_zero_left hz.symm
end Asakura.Chapter12
#print axioms Asakura.Chapter12.inverse_higher_derivative_formula
