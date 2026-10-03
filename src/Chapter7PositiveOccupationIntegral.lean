import Chapter7InfiniteIntervalOccupation
import Mathlib.Topology.Order.Compact

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1600000

/-- A continuous strictly positive function has a positive minimum on
[-1,1], so infinite occupation of that interval forces its time integral
also to be infinite. -/
theorem positive_integral_of_infinite_occupation
    {ι : Type*} [MeasurableSpace ι] (ν : Measure ι)
    (X : ι → ℝ) (hX : Measurable X) (a : ℝ → ℝ)
    (ha : Continuous a) (hap : ∀ x,0 < a x)
    (hocc : ν (X ⁻¹' Icc (-1:ℝ) 1) = ∞) :
    (∫⁻ t,ENNReal.ofReal (a (X t)) ∂ν) = ∞ := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (-1:ℝ) 1).Nonempty from ⟨0,by norm_num⟩) ha.continuousOn
  have hm : MeasurableSet (X ⁻¹' Icc (-1:ℝ) 1) := hX measurableSet_Icc
  have hb : (X ⁻¹' Icc (-1:ℝ) 1).indicator (fun _ => ENNReal.ofReal (a x)) ≤
      fun t => ENNReal.ofReal (a (X t)) := by
    intro t
    by_cases ht : t ∈ X ⁻¹' Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem ht]
      exact ENNReal.ofReal_le_ofReal (hmin ht)
    · rw [Set.indicator_of_notMem ht]
      exact bot_le
  have hh := lintegral_mono (μ := ν) hb
  rw [lintegral_indicator hm,lintegral_const,Measure.restrict_apply_univ,hocc,
    ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (hap x)))] at hh
  exact top_le_iff.mp hh

end Asakura.Chapter7
