import Chapter9GaussianMixture
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

open MeasureTheory
namespace Asakura.Chapter9
set_option maxHeartbeats 800000

/-- Equality of measures with continuous nonnegative densities gives
pointwise equality, not merely equality outside an exceptional set. -/
theorem continuous_density_unique {d : ℕ} (p q : (Fin d → ℝ) → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hp0 : ∀ x,0≤p x) (hq0 : ∀ x,0≤q x)
    (he : (volume : Measure (Fin d → ℝ)).withDensity (fun x => ENNReal.ofReal (p x))=
      volume.withDensity (fun x => ENNReal.ofReal (q x))) : p=q := by
  have hae := (withDensity_eq_iff_of_sigmaFinite hp.measurable.ennreal_ofReal.aemeasurable
    hq.measurable.ennreal_ofReal.aemeasurable).mp he
  apply (hp.ae_eq_iff_eq volume hq).mp
  filter_upwards [hae] with x hx
  have hh := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (hp0 x),ENNReal.toReal_ofReal (hq0 x)] using hh
end Asakura.Chapter9
