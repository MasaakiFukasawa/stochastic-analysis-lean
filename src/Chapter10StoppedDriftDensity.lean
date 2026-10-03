import Chapter10LocallyIntegrableDrift

open MeasureTheory Set Filter
namespace Asakura.Chapter10
set_option maxHeartbeats 1600000

/-- Stopping a drift primitive at T replaces its density by an indicator.
This density is measurable and locally integrable, even at its jump at T. -/
theorem stopped_drift_density (T : ℝ) (hT : 0≤T) (b : ℝ → ℝ) (hb : Continuous b) :
    Measurable ((Ioc (0:ℝ) T).indicator b) ∧
    (∀ a d,IntervalIntegrable ((Ioc (0:ℝ) T).indicator b) volume a d) ∧
    ∀ t,0≤t → (∫ s in 0..t,(Ioc (0:ℝ) T).indicator b s)=∫ s in 0..min T t,b s := by
  refine ⟨hb.measurable.indicator measurableSet_Ioc,?_,?_⟩
  · intro a d
    have hi := hb.intervalIntegrable (μ := volume) a d
    exact ⟨hi.1.indicator measurableSet_Ioc,hi.2.indicator measurableSet_Ioc⟩
  · intro t ht
    rw [intervalIntegral.integral_of_le ht,integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      intervalIntegral.integral_of_le (le_min hT ht)]
    have hs : Ioc (0:ℝ) T ∩ Ioc 0 t=Ioc 0 (min T t) := by
      ext s
      simp only [mem_inter_iff,mem_Ioc,le_min_iff]
      tauto
    rw [hs]

end Asakura.Chapter10
