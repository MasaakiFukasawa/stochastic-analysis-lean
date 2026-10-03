import Chapter12AsianPathAverage

open MeasureTheory Set
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

noncomputable def compactTimeMeasure (T : ℝ) (hT : 0 ≤ T) : Measure (Icc (0:ℝ) T) :=
  Measure.map (projIcc 0 T hT) (volume.restrict (Ioc (0:ℝ) T))

instance compactTimeMeasure_finite (T : ℝ) (hT : 0 ≤ T) : IsFiniteMeasure (compactTimeMeasure T hT) := by
  unfold compactTimeMeasure
  infer_instance

/-- Integrating on the compact time type is exactly the ordinary time
integral appearing in the manuscript, including its endpoint convention. -/
theorem compact_time_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (hT : 0 ≤ T) (f : ℝ → E) (hf : ContinuousOn f (Icc (0:ℝ) T)) :
    (∫ t : Icc (0:ℝ) T,f t.val ∂compactTimeMeasure T hT) = ∫ t in 0..T,f t := by
  have hc : Continuous (fun t : Icc (0:ℝ) T => f t.val) := hf.restrict
  unfold compactTimeMeasure
  rw [integral_map (continuous_projIcc (a := 0) (b := T) (h := hT)).measurable.aemeasurable hc.stronglyMeasurable.aestronglyMeasurable,
    intervalIntegral.integral_of_le hT]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [projIcc_of_mem hT ⟨ht.1.le,ht.2⟩]

end Asakura.Chapter12
