import Chapter3QuadraticApproximationProperty
import Chapter2SignedMeasureIdentification
import Chapter2SignedDifferenceIntegral

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Polarization identifies the canonical BV signed measure itself,
not merely its values on a selected collection of partition intervals. -/
theorem polarized_stieltjes_measure
    (d : ℝ) (hd : 0 ≤ d) (A B C : ℝ → ℝ)
    (hA : MonotoneOn A (Icc 0 d)) (hB : MonotoneOn B (Icc 0 d))
    (hrA : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt A (Icc 0 d ∩ Ici x) x)
    (hrB : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt B (Icc 0 d ∩ Ici x) x)
    (hC : BoundedVariationOn (C ∘ intervalClamp 0 d hd) univ)
    (hrC : ∀ x, ContinuousWithinAt (C ∘ intervalClamp 0 d hd) (Ici x) x)
    (he : ∀ x ∈ Icc 0 d, A x-B x = C x) :
    letI := intervalStieltjes_finite 0 d hd A hA hrA
    letI := intervalStieltjes_finite 0 d hd B hB hrB
    bvSigned (C ∘ intervalClamp 0 d hd) hC hrC 0 =
      (intervalStieltjes 0 d hd A hA hrA).measure.toSignedMeasure-
      (intervalStieltjes 0 d hd B hB hrB).measure.toSignedMeasure := by
  letI := intervalStieltjes_finite 0 d hd A hA hrA
  letI := intervalStieltjes_finite 0 d hd B hB hrB
  apply signed_measure_ext_Ioc
  intro a b hab
  rw [bvSigned_Ioc _ _ _ _ _ _ hab.le,VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
    Measure.toSignedMeasure_apply_measurable measurableSet_Ioc,
    intervalStieltjes_Ioc_real _ _ _ _ _ _ _ _ hab.le,
    intervalStieltjes_Ioc_real _ _ _ _ _ _ _ _ hab.le]
  have ha := he _ (intervalClamp_mem 0 d hd a)
  have hb := he _ (intervalClamp_mem 0 d hd b)
  dsimp only [Function.comp_def]
  linarith

/-- Continuous weights on [0,T) are integrable for the finite Stieltjes
measure on [0,d]. No global boundedness or behavior at T is required. -/
theorem continuous_weight_stieltjes_integrable
    {T : EReal} [Fact (0 ≤ T)] (d : ℝ) (hd : 0 ≤ d) (hdT : (d:EReal) < T)
    (H : ClosedTime T → ℝ) (hH : ∀ t, t < ⊤ → ContinuousAt H t)
    (A : ℝ → ℝ) (hA : MonotoneOn A (Icc 0 d))
    (hrA : ∀ x, x ∈ Icc 0 d → ContinuousWithinAt A (Icc 0 d ∩ Ici x) x) :
    Integrable (fun r => H (realTimeClamp r)) (intervalStieltjes 0 d hd A hA hrA).measure := by
  let μ := (intervalStieltjes 0 d hd A hA hrA).measure
  letI : IsFiniteMeasure μ := intervalStieltjes_finite 0 d hd A hA hrA
  have hdt : realTimeClamp (T := T) d < ⊤ := by
    change (realTimeClamp d : EReal) < T
    rw [real_time_clamp_eq d hd hdT.le]
    exact hdT
  have hc : Continuous (fun t => H (min (realTimeClamp d) t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hH _ ((min_le_left _ _).trans_lt hdt)).comp
      (continuous_const.min continuous_id).continuousAt
  let f : C(ClosedTime T,ℝ) := ⟨_,hc⟩
  have hg : Integrable (fun r => f (realTimeClamp r)) μ := by
    have hm : MemLp (fun r => f (realTimeClamp r)) 1 μ :=
      MemLp.of_bound (f.continuous.comp real_time_clamp_continuous).measurable.aestronglyMeasurable
        ‖f‖ (.of_forall (fun r => f.norm_coe_le_norm _))
    exact hm.integrable le_rfl
  apply hg.congr
  filter_upwards [interval_stieltjes_ae_mem_Ioc 0 d hd A hA hrA] with r hr
  exact congrArg H (min_eq_right (real_time_clamp_mono hr.2))

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.polarized_stieltjes_measure
#print axioms Asakura.Chapter3Complete.continuous_weight_stieltjes_integrable
