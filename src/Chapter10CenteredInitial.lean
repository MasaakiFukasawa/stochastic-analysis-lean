import Chapter10AugmentedInitial
import Chapter10KalmanAugmentedAlgebra

open MeasureTheory ProbabilityTheory Matrix Set
namespace Asakura.Chapter10
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Center the manuscript's Gaussian initial state at its stated mean.
This supplies the centered input, without requiring a nonsingular covariance. -/
theorem centered_gaussian_initial {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (F : MeasurableSpace Ω) (hle : F≤m) (X : Ω → Fin d → ℝ)
    (hX : Measurable[F] X) (hg : HasGaussianLaw X P) (m0 : Fin d → ℝ)
    (hmean : ∫ w,X w ∂P=m0) :
    Measurable[F] (fun w => X w-m0) ∧ HasGaussianLaw (fun w => X w-m0) P ∧
      (∫ w,X w-m0 ∂P)=0 := by
  letI : MeasurableSpace Ω := m
  have hm : Measurable[F] (fun w => X w-m0) := hX.sub measurable_const
  refine ⟨hm,?_,?_⟩
  · haveI := hg.isGaussian_map
    refine ⟨(hm.mono hle le_rfl).aemeasurable,?_⟩
    have he : P.map (fun w => X w-m0)=(P.map X).map (fun x => x-m0) := by
      rw [Measure.map_map (by fun_prop) (hX.mono hle le_rfl)]
      rfl
    rw [he]
    infer_instance
  · rw [integral_sub hg.integrable (integrable_const _),hmean,integral_const]
    simp

/-- The block map used in the actual error equation sends (X0,m0,0)
to (X0-m0,0), exactly the initial state used by the independence proof. -/
theorem kalman_initial_error {d r : ℕ} (x m0 : Fin d → ℝ) :
    finiteBlocks (differenceMatrix d) (0 : Matrix (Fin d) (Fin r) ℝ)
      (0 : Matrix (Fin r) (Fin (d+d)) ℝ) (1 : Matrix (Fin r) (Fin r) ℝ) *ᵥ
      extendZero (r := r) ((Sum.elim x m0) ∘ finSumFinEquiv.symm)=
        extendZero (r := r) (x-m0) := by
  have hd : differenceMatrix d*ᵥ((Sum.elim x m0) ∘ finSumFinEquiv.symm)=x-m0 := by
    ext i
    rw [differenceMatrix_action]
    simp only [headIndex,tailIndex,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,Pi.sub_apply]
  simp only [finiteBlocks,extendZero,submatrix_mulVec_equiv,fromBlocks_mulVec,
    Matrix.zero_mulVec,Matrix.one_mulVec,add_zero,zero_add,Equiv.symm_symm,
    Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id,Sum.elim_comp_inl,Sum.elim_comp_inr]
  simpa only [hd]

end Asakura.Chapter10
