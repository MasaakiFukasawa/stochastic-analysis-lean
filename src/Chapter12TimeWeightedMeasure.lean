import Chapter2WeightedHilbert
import Chapter2StieltjesRestriction
import Chapter12CompactTimeMeasure

open MeasureTheory ProbabilityTheory Set
namespace Asakura.Chapter12
open Asakura.Chapter2Complete Asakura.FullAudit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem time_interval_stieltjes (T : ℝ) (hT : 0 ≤ T) :
    (intervalStieltjes 0 T hT id (monotone_id.monotoneOn _)
      (fun x _ => continuous_id.continuousWithinAt)).measure = volume.restrict (Ioc 0 T) := by
  letI := intervalStieltjes_finite 0 T hT id (monotone_id.monotoneOn _)
    (fun x _ => continuous_id.continuousWithinAt)
  apply Measure.ext_of_Iic
  intro r
  rw [StieltjesFunction.measure_Iic _ (interval_stieltjes_left_limit 0 T hT (fun _ : Unit => id)
    (fun _ => (monotone_id.monotoneOn _)) (fun _ x _ => continuous_id.continuousWithinAt) ()),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Ioc_inter_Iic,Real.volume_Ioc]
  change ENNReal.ofReal (max 0 (min T r)-0) = ENNReal.ofReal (min T r-0)
  rw [sub_zero,sub_zero,ENNReal.ofReal_max,ENNReal.ofReal_zero,max_eq_right (show 0 ≤ ENNReal.ofReal (min T r) from bot_le)]

theorem time_weighted_path_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (hT : 0 ≤ T) :
    weightedPathMeasure P 0 T hT (fun _ t => t) (fun _ => (monotone_id.monotoneOn _))
      (fun _ x _ => continuous_id.continuousWithinAt) (fun _ => measurable_const) =
      P.prod (compactTimeMeasure T hT) := by
  have hk : randomStieltjesKernel 0 T hT (fun _ : Ω => fun t : ℝ => t) (fun _ => (monotone_id.monotoneOn _))
      (fun _ x _ => continuous_id.continuousWithinAt) (fun _ => measurable_const) =
      Kernel.const Ω (volume.restrict (Ioc 0 T)) := by
    ext w s hs
    change (intervalStieltjes 0 T hT id (monotone_id.monotoneOn _)
      (fun x _ => continuous_id.continuousWithinAt)).measure s = _
    rw [time_interval_stieltjes]
    rfl
  unfold weightedPathMeasure compactTimeMeasure
  rw [hk,Measure.compProd_const]
  have he := Measure.map_prod_map P (volume.restrict (Ioc 0 T)) measurable_id
    (continuous_projIcc (a := 0) (b := T) (h := hT)).measurable
  simpa only [Measure.map_id,Prod.map_def,id_eq] using he.symm

end Asakura.Chapter12
