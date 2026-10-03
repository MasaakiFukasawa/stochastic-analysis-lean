import Chapter10StateMeanContinuity

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma weighted_mean_regular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (hm : Measurable X) (hX : MemLp X 2 P)
    (η : Ω → ℝ) (hη : MemLp η 2 P) :
    Continuous (fun s => ∫ w,η w • X w (projIcc 0 T hT s) ∂P) ∧
      ∀ s,Integrable (fun w => η w • X w (projIcc 0 T hT s)) P := by
  have hi : Integrable (fun w => ‖η w‖*‖X w‖) P := hη.norm.integrable_mul hX.norm
  have hm' s : AEStronglyMeasurable (fun w => η w • X w (projIcc 0 T hT s)) P :=
    hη.aestronglyMeasurable.smul ((continuous_eval_const _).measurable.comp hm).aestronglyMeasurable
  have hb s w : ‖η w • X w (projIcc 0 T hT s)‖≤‖η w‖*‖X w‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((X w).norm_coe_le_norm _) (norm_nonneg _)
  refine ⟨?_,fun s => hi.mono' (hm' s) (ae_of_all _ fun w => hb s w)⟩
  apply continuousOn_univ.mp
  apply continuousOn_of_dominated (fun s _ => hm' s) (fun s _ => ae_of_all _ fun w => hb s w) hi
  apply ae_of_all
  intro w
  have hc : Continuous (fun s => η w • X w (projIcc 0 T hT s)) :=
    (show Continuous (fun _ : ℝ => η w) from continuous_const).smul
      (show Continuous (fun s => X w (projIcc 0 T hT s)) from (X w).continuous.comp continuous_projIcc)
  exact hc.continuousOn

end Asakura.Chapter10
