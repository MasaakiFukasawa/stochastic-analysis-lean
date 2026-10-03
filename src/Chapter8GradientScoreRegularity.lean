import Chapter8PotentialDriftRegularity

open scoped BigOperators NNReal
namespace Asakura.Chapter8
attribute [local instance] scalarOpNormed scalarOpSpace scalarBiNormed scalarBiSpace
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- The C2 potentials with bounded Hessians give C1 globally Lipschitz
score coefficients after multiplication by the fixed inverse diffusion. -/
theorem gradient_score_regularity {d n p : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Fin d → ℝ) ≃L[ℝ] E)
    (U : Fin p → (Fin d → ℝ) → ℝ) (hU : ∀ k,ContDiff ℝ 2 (U k))
    (C : Fin p → ℝ≥0) (hC : ∀ k x,‖fderiv ℝ (fderiv ℝ (U k)) x‖≤(C k:ℝ))
    (A : Fin n → Fin d → ℝ) :
    ∃ K : Fin p → Fin n → ℝ≥0,
      (∀ k j,LipschitzWith (K k j) (fun x : E => -(∑ i,A j i*fderiv ℝ (U k) (e.symm x) (Pi.single i 1)))) ∧
      (∀ k j,ContDiff ℝ 1 (fun x : E => -(∑ i,A j i*fderiv ℝ (U k) (e.symm x) (Pi.single i 1)))) := by
  let Q : Fin n → ((Fin d → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    fun j => -(∑ i,A j i • ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1))
  have hQ j v : Q j v= -(∑ i,A j i*v (Pi.single i 1)) := by
    simp only [Q,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.apply_apply,smul_eq_mul]
  have hD k : ContDiff ℝ 1 (fderiv ℝ (U k)) := (contDiff_succ_iff_fderiv (n := 1)).mp (hU k) |>.2.2
  have hl k : LipschitzWith (C k) (fderiv ℝ (U k)) := by
    apply lipschitzWith_of_nnnorm_fderiv_le ((hD k).differentiable (by norm_num))
    intro x
    exact_mod_cast hC k x
  refine ⟨fun k j => ‖Q j‖₊*(C k*‖e.symm.toContinuousLinearMap‖₊),?_,?_⟩
  · intro k j
    have hh := (Q j).lipschitz.comp ((hl k).comp e.symm.toContinuousLinearMap.lipschitz)
    simpa only [Function.comp_def,hQ,ContinuousLinearEquiv.coe_coe] using hh
  · intro k j
    have hh := (Q j).contDiff.comp ((hD k).comp e.symm.contDiff)
    simpa only [Function.comp_def,hQ] using hh

end Asakura.Chapter8
