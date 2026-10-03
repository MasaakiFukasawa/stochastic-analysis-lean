import Chapter1WrittenInteger

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.EndToEnd

/-- The L1 convergence statement for an integrable equivalence class needs
no additional pointwise measurability assumption on the chosen function. -/
theorem conditional_integer_L1
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (G : ℤ → MeasurableSpace Ω) (hG : Monotone G) (hle : ∀ z, G z ≤ m)
    {X : Ω → ℝ} (hX : Integrable X P) :
    Tendsto (fun z => eLpNorm (P[X | G z] - P[X | ⨆ z, G z]) 1 P)
      atTop (𝓝 0) ∧
    Tendsto (fun z => eLpNorm (P[X | G z] - P[X | ⨅ z, G z]) 1 P)
      atBot (𝓝 0) := by
  let Y := hX.aestronglyMeasurable.mk X
  have hXY : X =ᵐ[P] Y := hX.aestronglyMeasurable.ae_eq_mk
  have hmY : Measurable Y := hX.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hY : Integrable Y P := hX.congr hXY
  have hnorm (K L : MeasurableSpace Ω) :
      eLpNorm (P[X | K] - P[X | L]) 1 P =
      eLpNorm (P[Y | K] - P[Y | L]) 1 P :=
    eLpNorm_congr_ae ((condExp_congr_ae hXY).sub (condExp_congr_ae hXY))
  simpa only [hnorm] using
    Asakura.Chapter1Written.conditional_integer_L1_written G hG hle hmY hY

end Asakura.EndToEnd

#print axioms Asakura.EndToEnd.conditional_integer_L1
