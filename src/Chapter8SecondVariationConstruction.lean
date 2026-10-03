import Chapter8VariationalConstruction

open MeasureTheory Set
open scoped NNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Construct the bilinear second variational equation. Only continuity
of the second drift derivative is required; no third drift derivative is
introduced. Identifying this process as the second derivative is separate. -/
theorem second_variation_exists {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 ≤ T) (D : ℝ → E →L[ℝ] E)
    (D₂ : ℝ → E →L[ℝ] E →L[ℝ] E) (J : ℝ → E →L[ℝ] E)
    (hcD : Continuous D) (hcD₂ : Continuous D₂) (hcJ : Continuous J)
    (L : ℝ≥0) (hb : ∀ t,‖D t‖ ≤ (L:ℝ)) :
    ∃ K : ℝ → E →L[ℝ] E →L[ℝ] E,Continuous K ∧
      ∀ t,t∈Icc 0 T → ∀ h k,
        K t h k=∫ s in 0..t,D s (K s h k)+D₂ s (J s h) (J s k) := by
  let A := fun t => ContinuousLinearMap.compL ℝ E E E (D t)
  let R := fun t => ((ContinuousLinearMap.compL ℝ E E E).flip (J t)).comp ((D₂ t).comp (J t))
  have hcA : Continuous A := continuous_const.clm_apply hcD
  have hcR : Continuous R := (continuous_const.clm_apply hcJ).clm_comp (hcD₂.clm_comp hcJ)
  have hA t : ‖A t‖ ≤ (L:ℝ) := by
    exact ((ContinuousLinearMap.compL ℝ E E E).le_opNorm (D t)).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compL_le ℝ E E E) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hb t))
  have hc : Continuous (fun p : ℝ × (E →L[ℝ] E →L[ℝ] E) => (A p.1).comp p.2+R p.1) :=
    ((hcA.comp continuous_fst).clm_comp continuous_snd).add (hcR.comp continuous_fst)
  have hLip t : LipschitzWith L (fun K : E →L[ℝ] E →L[ℝ] E => (A t).comp K+R t) := by
    apply LipschitzWith.of_dist_le_mul
    intro K Q
    rw [dist_eq_norm,dist_eq_norm,add_sub_add_right_eq_sub,← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hA t) (norm_nonneg _))
  obtain ⟨K,hKc,hK⟩ := forced_integral_equation_exists T hT L
    (fun t K => (A t).comp K+R t) hc hLip (fun _ => 0) continuous_const
  refine ⟨K,hKc,?_⟩
  intro t ht h k
  have he := congrArg (fun B : E →L[ℝ] E →L[ℝ] E => B h k) (hK t ht)
  simp only [zero_add] at he
  rw [ContinuousLinearMap.intervalIntegral_apply (φ := fun s => (A s).comp (K s)+R s)
      (((hcA.clm_comp hKc).add hcR).intervalIntegrable 0 t),
    ContinuousLinearMap.intervalIntegral_apply (φ := fun s => ((A s).comp (K s)+R s) h)
      ((((hcA.clm_comp hKc).add hcR).clm_apply continuous_const).intervalIntegrable 0 t)] at he
  exact he

end Asakura.Chapter8
