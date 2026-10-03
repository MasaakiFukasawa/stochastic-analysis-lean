import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
namespace Asakura.Chapter12

theorem real_density_ae_equality {E:Type*} [MeasurableSpace E]
    (μ:Measure E) [SigmaFinite μ] (p q:E → ℝ) (hp:Measurable p) (hq:Measurable q)
    (hpn:∀ᵐx∂μ,0≤p x) (hqn:∀ᵐx∂μ,0≤q x)
    (he:μ.withDensity (fun x => ENNReal.ofReal (p x))=μ.withDensity (fun x => ENNReal.ofReal (q x))) :
    p=ᵐ[μ] q := by
  have h := (withDensity_eq_iff_of_sigmaFinite hp.ennreal_ofReal.aemeasurable hq.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [h,hpn,hqn] with x hx hp hq
  have ht := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal hq] using ht
end Asakura.Chapter12
#print axioms Asakura.Chapter12.real_density_ae_equality
