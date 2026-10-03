import Chapter12FinitePastFuture
import Chapter12TimeDirectionContinuity
import Chapter12SingleCoordinateIsometry
import Chapter12CompactTimeMeasure

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem finite_prefix_terminal_inner (T t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    inner ℝ (finiteTimeIntervalVector T 0 t) (finiteTimeIntervalVector T 0 T) = t := by
  have h := finite_interval_past_future T t t T (le_refl t)
  rw [←finite_time_interval_difference T t T ht htT,inner_sub_right,real_inner_self_eq_norm_sq,
    finite_time_interval_norm T 0 t (le_refl 0) ht htT,sub_zero,Real.sq_sqrt ht] at h
  exact sub_eq_zero.mp h

theorem integrated_prefix_terminal_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (T : ℝ) (hT : 0 ≤ T) (a : Icc (0:ℝ) T → ℝ) (ha : Continuous a) (σ : ℝ) :
    inner ℝ (∫ t : Icc (0:ℝ) T,a t • (σ • singleCoordinateIsometry i (finiteTimeIntervalVector T 0 t.val))
      ∂compactTimeMeasure T hT)
      (singleCoordinateIsometry i (finiteTimeIntervalVector T 0 T)) =
      σ * ∫ t : Icc (0:ℝ) T,t.val*a t ∂compactTimeMeasure T hT := by
  let J := singleCoordinateIsometry (H := Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i
  let U := fun t : Icc (0:ℝ) T => a t • (σ • J (finiteTimeIntervalVector T 0 t.val))
  have hc : Continuous U := ha.smul ((J.continuous.comp (finite_time_prefix_continuous T)).const_smul σ)
  have hi := hc.integrable_of_hasCompactSupport (μ := compactTimeMeasure T hT) (HasCompactSupport.of_compactSpace _)
  let L : PiLp 2 (fun _ : ι => Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) →L[ℝ] ℝ :=
    innerSL ℝ (J (finiteTimeIntervalVector T 0 T))
  have he := L.integral_comp_comm hi
  change (∫ t,L (U t) ∂compactTimeMeasure T hT) =
    inner ℝ (J (finiteTimeIntervalVector T 0 T)) (∫ t,U t ∂compactTimeMeasure T hT) at he
  rw [real_inner_comm] at he
  rw [←he,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  change inner ℝ (J (finiteTimeIntervalVector T 0 T)) (a t • (σ • J (finiteTimeIntervalVector T 0 t.val))) = _
  rw [inner_smul_right,inner_smul_right,J.inner_map_map,real_inner_comm,
    finite_prefix_terminal_inner T t.val t.property.1 t.property.2]
  ring

end Asakura.Chapter12
