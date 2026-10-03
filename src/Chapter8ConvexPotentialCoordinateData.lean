import Chapter8HilbertGradient
import Chapter8LinearCoordinateDerivatives
import Chapter8GibbsIntegrability
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped BigOperators RealInnerProductSpace NNReal
namespace Asakura.Chapter8
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's C3 and two-sided Hessian bounds supply the actual
coordinate gradient, bounded derivatives and Gibbs moment condition required
by the SDE construction and invariance proof. -/
theorem convex_potential_coordinate_data {d : ℕ}
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (hU : ContDiff ℝ 3 U)
    (κ L β : ℝ) (hκ : 0<κ) (hκL : κ≤L) (hβ : 0<β)
    (hb : ∀ x z,κ*‖z‖^2≤fderiv ℝ (fderiv ℝ U) x z z ∧
      fderiv ℝ (fderiv ℝ U) x z z≤L*‖z‖^2)
    (A₃ : ℝ≥0) (h₃ : ∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖≤(A₃:ℝ)) :
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    let V := fun x => U (e x)
    ∃ (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      (H : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
      (C₂ C₃ : ℝ≥0),
      (∀ x,HasFDerivAt g (H x) x) ∧ Continuous H ∧
      (∀ x,(H x).toLinearMap.IsSymmetric) ∧
      (∀ x z,κ*‖z‖^2≤⟪z,H x z⟫ ∧ ⟪z,H x z⟫≤L*‖z‖^2) ∧
      (∀ q,g (e q)=e (fun i => fderiv ℝ V q (Pi.single i 1))) ∧
      ContDiff ℝ 3 V ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ V) x‖≤(C₂:ℝ)) ∧
      (∀ x,‖fderiv ℝ (fderiv ℝ (fderiv ℝ V)) x‖≤(C₃:ℝ)) ∧
      Integrable (fun x : Fin d → ℝ => (1+∑ i,x i^2)*Real.exp (-β*V x)) := by
  dsimp only
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let V := fun x => U (e x)
  obtain ⟨g,H,hUg,hd,hH,hs,hB,hHb⟩ := hilbert_gradient_hessian U (hU.of_le (by norm_num)) κ L hκ hκL hb
  have hDf : (fun x => innerSL ℝ (g x))=fderiv ℝ U := by
    funext x
    exact (hUg x).fderiv.symm
  have h₂ x : ‖fderiv ℝ (fderiv ℝ U) x‖≤L := by
    have hh := (innerSL ℝ).hasFDerivAt.comp x (hd x)
    change HasFDerivAt (fun x => innerSL ℝ (g x)) ((innerSL ℝ).comp (H x)) x at hh
    rw [hDf] at hh
    rw [hh.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (hκ.le.trans hκL)
    intro z
    change ‖innerSL ℝ (H x z)‖≤L*‖z‖
    rw [innerSL_apply_norm]
    exact (H x).le_opNorm z |>.trans (mul_le_mul_of_nonneg_right (hHb x) (norm_nonneg z))
  obtain ⟨C₂,C₃,hC₂,hC₃⟩ := linear_coordinate_derivative_bounds e.toContinuousLinearMap U hU
    ⟨L,hκ.le.trans hκL⟩ A₃ h₂ h₃
  have hi := (strongly_convex_gibbs_integrability U g H κ β hκ hβ hUg hd (fun x z => (hB x z).1)).1
  have hi' := (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_of_integrable hi
  refine ⟨g,H,C₂,C₃,hd,hH,hs,hB,?_,hU.comp e.contDiff,hC₂,hC₃,?_⟩
  · intro q
    ext i
    have hh := (hUg (e q)).comp q e.hasFDerivAt
    change HasFDerivAt V ((innerSL ℝ (g (e q))).comp e.toContinuousLinearMap) q at hh
    have hh' : fderiv ℝ V q (Pi.single i 1)=g (e q) i := by
      rw [hh.fderiv]
      change ⟪g (e q),EuclideanSpace.single i (1:ℝ)⟫=g (e q) i
      simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    exact hh'.symm
  · convert hi' using 1
    funext x
    dsimp only [Function.comp_def]
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl

end Asakura.Chapter8
