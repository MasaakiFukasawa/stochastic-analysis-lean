import Chapter10ConstructedCovariance
import Chapter10CovarianceContinuity

open MeasureTheory Set Filter
open scoped NNReal
namespace Asakura.Chapter10
set_option backward.isDefEq.respectTransparency false

/-- Dominated convergence applies to the linear-drift cross moment because
its absolute value is bounded by a constant times the squared path norm. -/
theorem linear_drift_moment_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {d : ℕ} (T : ℝ) (hT : 0≤T)
    (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ)) (hm : Measurable X) (hX : MemLp X 2 P)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K) (i j : Fin d) :
    Continuous (fun s => ∫ w,X w (projIcc 0 T hT s) j*(A s (X w (projIcc 0 T hT s))) i ∂P) := by
  let U := fun s w => X w (projIcc 0 T hT s)
  have hUm s : Measurable (U s) := (continuous_eval_const _).measurable.comp hm
  apply continuousOn_univ.mp
  apply continuousOn_of_dominated (bound := fun w => (K:ℝ)*‖X w‖^2)
  · intro s _
    exact (((measurable_pi_apply j).comp (hUm s)).mul
      ((measurable_pi_apply i).comp ((A s).continuous.measurable.comp (hUm s)))).aestronglyMeasurable
  · intro s _
    exact ae_of_all _ fun w => by
      have hu : ‖U s w‖≤‖X w‖ := (X w).norm_coe_le_norm _
      have hj : ‖U s w j‖≤‖X w‖ := (norm_le_pi_norm _ j).trans hu
      have ha : ‖(A s (U s w)) i‖≤(K:ℝ)*‖X w‖ :=
        (norm_le_pi_norm _ i).trans (((A s).le_opNorm _).trans
          (mul_le_mul (hAK s) hu (norm_nonneg _) K.coe_nonneg))
      change ‖U s w j*(A s (U s w)) i‖≤_
      rw [norm_mul]
      have hh := mul_le_mul hj ha (norm_nonneg _) (norm_nonneg (X w))
      nlinarith
  · exact hX.norm.integrable_sq.const_mul K
  · exact ae_of_all _ fun w => by
      have hc : Continuous (fun s => U s w) := (X w).continuous.comp continuous_projIcc
      exact (((continuous_apply j).comp hc).mul
        ((continuous_apply i).comp (hA.clm_apply hc))).continuousOn

end Asakura.Chapter10
