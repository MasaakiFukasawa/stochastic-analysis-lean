import Chapter5BackwardHeatExtension
import Chapter5AffineRestrictionHessian
import Mathlib.Analysis.Normed.Operator.Prod

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter5
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Chain rule and restriction of the Hessian turn the actual forward
heat equation into the zero generator of its backwards extension. -/
theorem backward_heat_extension_generator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (Q : (Fin n → ℝ) →L[ℝ] E) (A : ℝ → E → ℝ)
    (g : E × ℝ → ℝ) (hg : ContDiff ℝ 2 g) (b S : ℝ) (hb : b<S)
    (he : ∀ p : E × ℝ,p.2≤b → g =ᶠ[𝓝 p] (fun q => A (S-q.2) q.1))
    (hheat : ∀ x t,0<t → HasDerivAt (fun s => A s x)
      ((1/2:ℝ)*∑ i,fderiv ℝ (fderiv ℝ (A t)) x (Q (Pi.single i 1)) (Q (Pi.single i 1))) t)
    (p : E × ℝ) (hp : p.2≤b) :
    fderiv ℝ g p (0,1)+
      (1/2:ℝ)*∑ i,fderiv ℝ (fderiv ℝ g) p (Q (Pi.single i 1),0) (Q (Pi.single i 1),0)=0 := by
  have hgD := ((hg.differentiable (by norm_num)).differentiableAt (x := p)).hasFDerivAt
  have ht := hgD.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
  have hback := (hheat p.1 (S-p.2) (sub_pos.mpr (hp.trans_lt hb))).comp p.2
    ((hasDerivAt_const p.2 S).sub (hasDerivAt_id' p.2))
  have hl : (fun s => g (p.1,s)) =ᶠ[𝓝 p.2] (fun s => A (S-s) p.1) :=
    (he p hp).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hd := ht.unique (hback.congr_of_eventuallyEq hl)
  have hs : (fun x => g (x,p.2))=A (S-p.2) := by
    funext x
    exact (he (x,p.2) hp).eq_of_nhds
  have hess i : fderiv ℝ (fderiv ℝ (A (S-p.2))) p.1 (Q (Pi.single i 1)) (Q (Pi.single i 1))=
      fderiv ℝ (fderiv ℝ g) p (Q (Pi.single i 1),0) (Q (Pi.single i 1),0) := by
    rw [← hs]
    simpa using affine_restriction_hessian g hg (ContinuousLinearMap.inl ℝ E ℝ)
      (0,p.2) p.1 (Q (Pi.single i 1)) (Q (Pi.single i 1))
  simp only [zero_sub,mul_neg_one] at hd
  simp_rw [hess] at hd
  linarith

end Asakura.Chapter5
