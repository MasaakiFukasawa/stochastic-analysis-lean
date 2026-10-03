import Chapter8SymmetricNormBound
import Chapter8GibbsSkewGenerator

open scoped RealInnerProductSpace
namespace Asakura.Chapter8
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Construct the gradient and Hessian operator from the actual first and
second Frechet derivatives of U. Symmetry is proved by equality of mixed
derivatives, rather than imposed on an unrelated force field. -/
theorem hilbert_gradient_hessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (U : E → ℝ) (hU : ContDiff ℝ 2 U)
    (κ L : ℝ) (hκ : 0<κ) (hκL : κ≤L)
    (hb : ∀ x z,κ*‖z‖^2≤fderiv ℝ (fderiv ℝ U) x z z ∧
      fderiv ℝ (fderiv ℝ U) x z z≤L*‖z‖^2) :
    ∃ (g : E → E) (H : E → E →L[ℝ] E),
      (∀ x,HasFDerivAt U (innerSL ℝ (g x)) x) ∧
      (∀ x,HasFDerivAt g (H x) x) ∧ Continuous H ∧
      (∀ x,(H x).toLinearMap.IsSymmetric) ∧
      (∀ x z,κ*‖z‖^2≤⟪z,H x z⟫ ∧ ⟪z,H x z⟫≤L*‖z‖^2) ∧
      (∀ x,‖H x‖≤L) := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g := fun x => R (fderiv ℝ U x)
  let H := fun x => R.comp (fderiv ℝ (fderiv ℝ U) x)
  have hD : ContDiff ℝ 1 (fderiv ℝ U) := (contDiff_succ_iff_fderiv (n := 1)).mp hU |>.2.2
  have hgrad (x : E) : innerSL ℝ (g x)=fderiv ℝ U x := by
    ext z
    exact InnerProductSpace.toDual_symm_apply
  have hHx (x z w : E) : ⟪H x z,w⟫=fderiv ℝ (fderiv ℝ U) x z w :=
    InnerProductSpace.toDual_symm_apply
  have hs (x : E) : (H x).toLinearMap.IsSymmetric := by
    intro z w
    change ⟪H x z,w⟫=⟪z,H x w⟫
    rw [real_inner_comm (H x w) z,hHx,hHx]
    exact (hU.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq z w
  have hB (x z : E) : κ*‖z‖^2≤⟪z,H x z⟫ ∧ ⟪z,H x z⟫≤L*‖z‖^2 := by
    rw [real_inner_comm (H x z) z,hHx]
    exact hb x z
  refine ⟨g,H,?_,?_,?_,hs,hB,?_⟩
  · intro x
    rw [hgrad]
    exact (hU.differentiable (by norm_num) x).hasFDerivAt
  · intro x
    exact R.hasFDerivAt.comp x ((hD.differentiable (by norm_num) x).hasFDerivAt)
  · exact continuous_const.clm_comp (hD.continuous_fderiv (by norm_num))
  · intro x
    exact symmetric_norm_bound (H x) (hs x) L (hκ.le.trans hκL)
      (fun z => ⟨(mul_nonneg hκ.le (sq_nonneg _)).trans (hB x z).1,(hB x z).2⟩)

end Asakura.Chapter8
