import Chapter7ConditionalFailure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set Filter
open scoped ENNReal
namespace Asakura.Chapter7
set_option maxHeartbeats 1600000

/-- The two stopped-moment bounds control the no-hit event: either the
upper endpoint has been reached, or the deterministic time cap has been
reached. This is the estimate used before sending the cap to infinity. -/
theorem exit_probability_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X U : Ω → ℝ) (hX : Integrable X P) (hU : Integrable U P)
    (hx0 : 0 ≤ᵐ[P] X) (hu0 : 0 ≤ᵐ[P] U)
    (x R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hm : (∫ w,X w ∂P) = x) (ht : (∫ w,U w ∂P) ≤ R^2)
    (E : Set Ω) (he : ∀ᵐ w ∂P,w ∈ E → R ≤ X w ∨ c ≤ U w) :
    P.real E ≤ x/R+R^2/c := by
  have h1 := mul_meas_ge_le_integral_of_nonneg hx0 hX R
  have h2 := mul_meas_ge_le_integral_of_nonneg hu0 hU c
  rw [hm] at h1
  have hb1 : P.real {w | R ≤ X w} ≤ x/R := (le_div_iff₀ hR).mpr (by nlinarith)
  have hb2 : P.real {w | c ≤ U w} ≤ R^2/c := (le_div_iff₀ hc).mpr (by nlinarith)
  have hle : P E ≤ P {w | R ≤ X w}+P {w | c ≤ U w} := (measure_mono_ae he).trans (measure_union_le _ _)
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _,measure_ne_top _ _⟩) hle
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
  change P.real E ≤ P.real {w | R ≤ X w}+P.real {w | c ≤ U w} at hreal
  linarith

end Asakura.Chapter7
