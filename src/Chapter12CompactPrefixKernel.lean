import Chapter12CompactTimeMeasure
import Chapter12PrefixKernelIntegrable
import Chapter12SingleCoordinateIsometry

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem compact_prefix_L2_kernel (T : ℝ) (hT : 0 ≤ T) (a : ℝ → ℝ) (ha : Continuous a)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ∈ Ioc (0:ℝ) T, ‖a t‖ ≤ C) :
    ((∫ t : Icc (0:ℝ) T,a t.val • finiteTimeIntervalVector T 0 t.val ∂compactTimeMeasure T hT :
      Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) : ℝ → ℝ) =ᵐ[
      (volume.restrict (Ioi (0:ℝ))).restrict (Iic T)] (fun s => ∫ t in s..T,a t) := by
  have hc : ContinuousOn (fun t => a t • finiteTimeIntervalVector T 0 t) (Icc (0:ℝ) T) :=
    continuousOn_iff_continuous_restrict.mpr
      ((ha.comp continuous_subtype_val).smul (finite_time_prefix_continuous T))
  rw [compact_time_integral T hT _ hc,intervalIntegral.integral_of_le hT]
  exact bounded_integrated_prefix_L2_kernel T a ha.measurable C hC hb

/-- Moving a deterministic coordinate injection outside the time integral
identifies the vector Brownian direction with the scalar time kernel. -/
theorem coordinate_integral_prefix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (T : ℝ) (hT : 0 ≤ T) (a : ℝ → ℝ) (ha : Continuous a) (σ : ℝ) :
    (∫ t : Icc (0:ℝ) T,a t.val • (σ • singleCoordinateIsometry i (finiteTimeIntervalVector T 0 t.val))
      ∂compactTimeMeasure T hT) =
    singleCoordinateIsometry i (σ • ∫ t : Icc (0:ℝ) T,a t.val • finiteTimeIntervalVector T 0 t.val
      ∂compactTimeMeasure T hT) := by
  let J := (singleCoordinateIsometry (H := Lp ℝ 2 ((volume.restrict (Ioi (0:ℝ))).restrict (Iic T))) i).toContinuousLinearMap
  have hc : Continuous (fun t : Icc (0:ℝ) T => σ • (a t.val • finiteTimeIntervalVector T 0 t.val)) :=
    ((ha.comp continuous_subtype_val).smul (finite_time_prefix_continuous T)).const_smul σ
  have hi := hc.integrable_of_hasCompactSupport (μ := compactTimeMeasure T hT) (HasCompactSupport.of_compactSpace _)
  have he := J.integral_comp_comm hi
  rw [integral_smul] at he
  simpa only [J,map_smul,smul_smul,mul_comm,LinearIsometry.coe_toContinuousLinearMap] using he

end Asakura.Chapter12
