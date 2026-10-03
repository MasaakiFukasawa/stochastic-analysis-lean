import Chapter8StationaryTimeAverage
import Chapter8L1Approximation

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Asakura.Chapter8
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- The time-average variance estimate also yields the L1 convergence
needed before removing the information-matrix truncation. -/
theorem l1_limit_from_second_moments {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter I) (Z : I → Ω → ℝ)
    (hZ : ∀ i,MemLp (Z i) 2 P)
    (hlim : Tendsto (fun i => ∫ w,(Z i w)^2 ∂P) l (nhds 0)) :
    Tendsto (fun i => ∫ w,|Z i w| ∂P) l (nhds 0) := by
  have hb i : (∫ w,|Z i w| ∂P) ≤ Real.sqrt (∫ w,(Z i w)^2 ∂P) := by
    have hv := variance_nonneg (fun w => |Z i w|) P
    have hi : MemLp (fun w => |Z i w|) 2 P := (hZ i).norm
    rw [variance_eq_sub hi] at hv
    simp only [Pi.pow_apply,sq_abs] at hv
    apply (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
      (integral_nonneg (fun _ => sq_nonneg _))).mpr
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun i => Real.sqrt (∫ w,(Z i w)^2 ∂P)) l (nhds 0) from by
      simpa only [Function.comp_def,Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt (x := (0:ℝ))).tendsto.comp hlim)
    (fun i => integral_nonneg (fun _ => abs_nonneg _)) hb

end Asakura.Chapter8
