import Chapter10StateMeanEquation
import Chapter10CovarianceContinuity

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Continuous state paths with an integrable path norm have continuous means. -/
theorem state_mean_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (hm : Measurable X) (hX : MemLp X 2 P) :
    Continuous (fun s => ∫ w,X w (projIcc 0 T hT s) ∂P) := by
  apply continuousOn_univ.mp
  apply continuousOn_of_dominated (bound := fun w => ‖X w‖)
  · intro s _
    exact ((continuous_eval_const _).measurable.comp hm).aestronglyMeasurable
  · intro s _
    exact ae_of_all _ fun w => (X w).norm_coe_le_norm _
  · exact hX.norm.integrable (by norm_num)
  · exact ae_of_all _ fun w => ((X w).continuous.comp continuous_projIcc).continuousOn

lemma state_value_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (hm : Measurable X) (hX : MemLp X 2 P)
    (s : ℝ) : Integrable (fun w => X w (projIcc 0 T hT s)) P := by
  apply (hX.norm.integrable (by norm_num)).mono'
    ((continuous_eval_const _).measurable.comp hm).aestronglyMeasurable
  exact ae_of_all _ fun w => (X w).norm_coe_le_norm _

end Asakura.Chapter10
