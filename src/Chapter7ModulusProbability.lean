import Chapter7ContinuousModulus

open MeasureTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter7

lemma modulus_probability {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [CompactSpace E] [SecondCountableTopology E] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → C(E,ℝ)) (hf : ∀ t,Measurable (fun w => f w t))
    (h : ℕ → ℝ≥0) (hh : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n w => ‖modulusPath (f w) (h n)‖) atTop (fun _ => 0) := by
  exact tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_modulus f hf (h n)).aestronglyMeasurable)
    (ae_of_all P (fun w => continuous_modulus_zero (f w) h hh))

end Asakura.Chapter7
