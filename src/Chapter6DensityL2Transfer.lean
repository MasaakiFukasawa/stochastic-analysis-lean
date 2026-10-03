import Chapter6DensityConditional
import Chapter6ExponentialSecondMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter6

lemma square_integrable_density_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (d : Ω → ℝ≥0) (hd : Measurable d)
    (hQ : Q=P.withDensity (fun w => (d w:ℝ≥0∞)))
    (hd2 : MemLp (fun w => (d w:ℝ)) 2 P) (X : Ω → ℝ) (hX : MemLp X 2 P) :
    Integrable X Q := by
  rw [hQ]
  apply (integrable_withDensity_iff_integrable_coe_smul hd).mpr
  convert hd2.integrable_mul hX using 1

end Asakura.Chapter6
