import Chapter12VolterraVariations

open MeasureTheory Set
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem higherChainRemainder_one {E F G:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f:E → F) (g:F → G) (hf:ContDiff ℝ ∞ f) (hg:ContDiff ℝ ∞ g)
    (x:E) (v:Fin 1 → E) : higherChainRemainder f g 1 x v=0 := by
  have h := higher_chain_linear_split f g hf hg 0 x v
  change iteratedFDeriv ℝ 1 (g ∘ f) x v = fderiv ℝ g (f x) (iteratedFDeriv ℝ 1 f x v) + higherChainRemainder f g 1 x v at h
  rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply] at h
  rw [fderiv_comp x (hg.differentiable (by simp) (f x)) (hf.differentiable (by simp) x),
    ContinuousLinearMap.comp_apply] at h
  exact (add_left_cancel (h.symm.trans (add_zero _).symm))

theorem first_volterra_variation {E:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (b:E → E) (hb:ContDiff ℝ ∞ b)
    (hbound:∀k:ℕ,1≤k → ∃C:ℝ≥0,∀x,‖iteratedFDeriv ℝ k b x‖≤(C:ℝ))
    (T:ℝ) (hT:0≤T) (S:C(Icc (0:ℝ) T,E) → C(Icc (0:ℝ) T,E))
    (hS:ContDiff ℝ ∞ S)
    (heq:∀a t,S a t=a t+∫s in 0..t.val,b (S a (projIcc 0 T hT s)))
    (a h:C(Icc (0:ℝ) T,E)) (t:Icc (0:ℝ) T) :
    (fderiv ℝ S a h) t=h t+∫s in 0..t.val,
      fderiv ℝ b (S a (projIcc 0 T hT s)) ((fderiv ℝ S a h) (projIcc 0 T hT s)) := by
  have hd := volterra_parameter_variations b hb hbound T hT id S contDiff_id hS heq 0 a (fun _ => h) t
  change (iteratedFDeriv ℝ 1 S a (fun _ => h)) t = (iteratedFDeriv ℝ 1 id a (fun _ => h)) t + ∫s in 0..t.val, fderiv ℝ b (S a (projIcc 0 T hT s)) ((iteratedFDeriv ℝ 1 S a (fun _ => h)) (projIcc 0 T hT s)) + higherChainRemainder (fun y => S y (projIcc 0 T hT s)) b 1 a (fun _ => h) at hd
  simp_rw [iteratedFDeriv_one_apply,fderiv_id,ContinuousLinearMap.id_apply] at hd
  rw [hd]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  let ev : C(Icc (0:ℝ) T,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (projIcc 0 T hT s)
  have hf : ContDiff ℝ ∞ (fun y => S y (projIcc 0 T hT s)) :=
    ev.contDiff.comp hS
  rw [higherChainRemainder_one (fun y => S y (projIcc 0 T hT s)) b hf hb a (fun _ => h),add_zero]
end Asakura.Chapter12
#print axioms Asakura.Chapter12.first_volterra_variation
