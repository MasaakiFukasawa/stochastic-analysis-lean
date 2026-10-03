import Chapter12CompactPrefixKernel
import Chapter12FiniteCompactTime

open MeasureTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The time representative of the integrated prefix directions is the
remaining-time integral appearing in the Asian hedge. -/
theorem compact_prefix_time_kernel (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → ℝ) (ha : Continuous a) :
    (finiteTimeToCompact T hT
      (∫ t : Icc (0:ℝ) T,a t.val • finiteTimeIntervalVector T 0 t.val ∂compactTimeMeasure T hT) :
        Icc (0:ℝ) T → ℝ) =ᵐ[compactTimeMeasure T hT]
      (fun s => ∫ t in s.val..T,a t) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha.continuousOn
  have hk := compact_prefix_L2_kernel T hT a ha (max C 0) (le_max_right _ _)
    (fun t ht => (hC t ⟨ht.1.le,ht.2⟩).trans (le_max_left _ _))
  have hka := (compact_time_val_preserving T hT).quasiMeasurePreserving.ae hk
  have hc := Lp.coeFn_compMeasurePreserving
    (∫ t : Icc (0:ℝ) T,a t.val • finiteTimeIntervalVector T 0 t.val ∂compactTimeMeasure T hT)
    (compact_time_val_preserving T hT)
  exact hc.trans hka

end Asakura.Chapter12
