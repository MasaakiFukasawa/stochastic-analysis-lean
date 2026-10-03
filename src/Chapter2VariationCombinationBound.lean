import Chapter2IntegralPathVariationBound

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- Part (3) of rep252 using the actual dV measure characterized by
increments. No equality between an auxiliary dominating measure and |dA|
is assumed. The two left terms are the integrals against dV plus or minus dA. -/
theorem variation_measure_combination_bound
    (κ : Measure ℝ) (ξ : SignedMeasure ℝ) (hdom : ξ.totalVariation ≤ κ)
    (H : ℝ → ℝ) (hi : Integrable H κ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ r in S, |H r| ∂κ)+signedIntegralRaw ξ (S.indicator (fun r => |H r|)) ≤
      2*(∫ r in S, |H r| ∂κ) ∧
    (∫ r in S, |H r| ∂κ)-signedIntegralRaw ξ (S.indicator (fun r => |H r|)) ≤
      2*(∫ r in S, |H r| ∂κ) := by
  have h := signed_integral_absolute_bound ξ (S.indicator (fun r => |H r|))
    ((hi.abs.mono_measure hdom).indicator hS)
  have he : (fun r => |S.indicator (fun r => |H r|) r|) = S.indicator (fun r => |H r|) := by
    funext r
    by_cases hr : r ∈ S <;> simp [hr]
  rw [he,integral_indicator hS] at h
  have hle : (∫ r in S, |H r| ∂ξ.totalVariation) ≤ ∫ r in S, |H r| ∂κ := integral_mono_measure (Measure.restrict_mono le_rfl hdom)
    (.of_forall (fun r => abs_nonneg (H r))) hi.abs.integrableOn
  have hh := abs_le.mp (h.trans hle)
  constructor <;> linarith [hh.1,hh.2]

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.variation_measure_combination_bound
