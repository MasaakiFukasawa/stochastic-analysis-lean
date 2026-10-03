import Chapter6PositiveDensityWritten

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace Asakura.Chapter6
set_option maxHeartbeats 2400000

lemma affine_drift_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (x : E) (f : E → E) (C : ℝ) (hC : 0≤C)
    (hf : ∀ y,‖f y‖≤C*(1+‖y‖)) (w : E) :
    ‖L.symm (f (x+L w))‖≤
      (‖L.symm.toContinuousLinearMap‖*C*(1+‖x‖+‖L.toContinuousLinearMap‖))*(1+‖w‖) := by
  have hx : ‖x+L w‖≤‖x‖+‖L.toContinuousLinearMap‖*‖w‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl (L.toContinuousLinearMap.le_opNorm w))
  have hf' := (L.symm.toContinuousLinearMap.le_opNorm (f (x+L w))).trans
    (mul_le_mul_of_nonneg_left (hf (x+L w)) (norm_nonneg _))
  change ‖L.symm (f (x+L w))‖≤‖L.symm.toContinuousLinearMap‖*(C*(1+‖x+L w‖)) at hf'
  have hh := mul_le_mul_of_nonneg_left hx (mul_nonneg (norm_nonneg L.symm.toContinuousLinearMap) hC)
  have hpos := mul_nonneg (mul_nonneg (norm_nonneg L.symm.toContinuousLinearMap) hC)
    (mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (norm_nonneg w))
  have hp := mul_nonneg (mul_nonneg (norm_nonneg L.symm.toContinuousLinearMap) hC) (norm_nonneg L.toContinuousLinearMap)
  nlinarith

/-- The manuscript's growth condition in the original state coordinates
implies the condition used in the Brownian reference coordinates. -/
theorem affine_transformed_linear_growth {d : ℕ}
    (L : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ)
    (μ : ℝ × (Fin d → ℝ) → Fin d → ℝ) (C : ℝ) (hC : 0≤C)
    (hμ : ∀ z,‖WithLp.toLp 2 (μ z)‖≤C*(1+‖WithLp.toLp 2 z.2‖)) :
    ∃ K : ℝ,0≤K ∧ ∀ r y,‖WithLp.toLp 2 (L.symm (μ (r,x+L y)))‖≤K*(1+‖WithLp.toLp 2 y‖) := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin d => ℝ)).symm
  let A := (e.symm.trans L).trans e
  let K := ‖A.symm.toContinuousLinearMap‖*C*(1+‖e x‖+‖A.toContinuousLinearMap‖)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro r y
  have h := affine_drift_growth A (e x) (fun v => e (μ (r,e.symm v))) C hC
    (fun v => by
      have hh := hμ (r,e.symm v)
      change ‖e (μ (r,e.symm v))‖≤C*(1+‖e (e.symm v)‖) at hh
      simpa only [e.apply_symm_apply] using hh) (e y)
  have hsum : e.symm (e x+A (e y))=x+L y := by
    simp only [A,ContinuousLinearEquiv.trans_apply,map_add,e.symm_apply_apply]
  rw [hsum] at h
  change ‖A.symm (e (μ (r,x+L y)))‖≤K*(1+‖e y‖) at h
  have hsym (v : Fin d → ℝ) : A.symm (e v)=e (L.symm v) := by
    apply A.injective
    rw [A.apply_symm_apply]
    simp only [A,ContinuousLinearEquiv.trans_apply,e.symm_apply_apply,L.apply_symm_apply]
  rw [hsym] at h
  exact h

end Asakura.Chapter6
