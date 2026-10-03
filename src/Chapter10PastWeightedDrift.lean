import Chapter10LinearMeanFubini
import Chapter10StateMeanContinuity

open MeasureTheory Set Filter
open scoped NNReal
namespace Asakura.Chapter10
open Asakura.Chapter8
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Fubini and continuity for a drift multiplied by an earlier L2 variable.
Cauchy--Schwarz supplies the needed integrable envelope. -/
theorem past_weighted_drift_regular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (T : ℝ) (hT : 0≤T) (X : Ω → C(Icc (0:ℝ) T,Fin d → ℝ))
    (hm : Measurable X) (hX : MemLp X 2 P)
    (η : Ω → ℝ) (hη : MemLp η 2 P)
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Continuous A)
    (K : ℝ≥0) (hAK : ∀ s,‖A s‖≤K) (i : Fin d) :
    let f := fun w s => η w*(A s (X w (projIcc 0 T hT s))) i
    Continuous (fun s => ∫ w,f w s ∂P) ∧
      ∀ r,0≤r → Integrable (fun w => ∫ s in 0..r,f w s) P ∧
        (∫ w,(∫ s in 0..r,f w s) ∂P)=∫ s in 0..r,∫ w,f w s ∂P := by
  let U := fun s w => X w (projIcc 0 T hT s)
  let f := fun w s => η w*(A s (U s w)) i
  have hc w : Continuous (f w) := continuous_const.mul
    ((continuous_apply i).comp (hA.clm_apply ((X w).continuous.comp continuous_projIcc)))
  have ham s : AEStronglyMeasurable (fun w => f w s) P := hη.aestronglyMeasurable.mul
    (((continuous_apply i).comp (A s).continuous).measurable.comp
      ((continuous_eval_const _).measurable.comp hm)).aestronglyMeasurable
  let D := fun w => (K:ℝ)*(‖η w‖*‖X w‖)
  have hD : Integrable D P := (hη.norm.integrable_mul hX.norm).const_mul K
  have hb w s : ‖f w s‖≤D w := by
    have hu : ‖U s w‖≤‖X w‖ := (X w).norm_coe_le_norm _
    have ha : ‖(A s (U s w)) i‖≤(K:ℝ)*‖X w‖ :=
      (norm_le_pi_norm _ i).trans (((A s).le_opNorm _).trans
        (mul_le_mul (hAK s) hu (norm_nonneg _) K.coe_nonneg))
    change ‖η w*(A s (U s w)) i‖≤_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans_eq (by dsimp [D]; ring)
  refine ⟨?_,?_⟩
  · apply continuousOn_univ.mp
    exact continuousOn_of_dominated (fun s _ => ham s)
      (fun s _ => ae_of_all _ fun w => hb w s) hD (ae_of_all _ fun w => (hc w).continuousOn)
  · intro r hr
    let η' := hη.aestronglyMeasurable.mk η
    have hη'e : η=ᵐ[P] η' := hη.aestronglyMeasurable.ae_eq_mk
    let f' := fun w s => η' w*(A s (U s w)) i
    have hmc s : Measurable (fun w => f' w s) := hη.aestronglyMeasurable.stronglyMeasurable_mk.measurable.mul
      (((continuous_apply i).comp (A s).continuous).measurable.comp ((continuous_eval_const _).measurable.comp hm))
    have hcc w : Continuous (f' w) := continuous_const.mul
      ((continuous_apply i).comp (hA.clm_apply ((X w).continuous.comp continuous_projIcc)))
    have hh := dynkin_fubini P r hr f'
      ((measurable_uncurry_of_continuous_of_measurable hcc hmc).comp measurable_swap) D hD
      (by filter_upwards [hη'e] with w hw; intro s _; simpa only [f',f,←hw] using hb w s)
    have he : (fun w => ∫ s in 0..r,f w s)=ᵐ[P] fun w => ∫ s in 0..r,f' w s :=
      hη'e.mono (fun w hw => by simp only [f,f',U,hw])
    refine ⟨hh.1.congr he.symm,?_⟩
    rw [integral_congr_ae he,hh.2]
    apply intervalIntegral.integral_congr
    intro s _
    exact integral_congr_ae (hη'e.mono (fun w hw => by simp only [f,f',U,hw])) |>.symm

end Asakura.Chapter10
