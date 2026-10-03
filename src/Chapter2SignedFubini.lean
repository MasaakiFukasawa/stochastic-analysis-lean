import Chapter2SignedIntegralEstimate
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
namespace Asakura.Chapter2Complete
open Asakura.FullAudit
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

/-- Ordinary Fubini for the actual positive-minus-negative signed integral,
with absolute integrability measured by total variation. -/
theorem signed_integral_fubini
    {E S : Type*} [MeasurableSpace E] [MeasurableSpace S]
    (μ : Measure E) [SigmaFinite μ] (ν : SignedMeasure S) (H : E × S → ℝ)
    (hH : Integrable H (μ.prod ν.totalVariation)) :
    Integrable (fun x => signedIntegralRaw ν (fun r => H (x,r))) μ ∧
    Integrable (fun r => ∫ x, H (x,r) ∂μ) ν.totalVariation ∧
    (∫ x, signedIntegralRaw ν (fun r => H (x,r)) ∂μ) =
      signedIntegralRaw ν (fun r => ∫ x, H (x,r) ∂μ) := by
  have hp : ν.toJordanDecomposition.posPart ≤ ν.totalVariation := by intro s; exact le_add_right le_rfl
  have hn : ν.toJordanDecomposition.negPart ≤ ν.totalVariation := by intro s; exact le_add_left le_rfl
  have hip := hH.mono_measure (Measure.prod_mono le_rfl hp)
  have hin := hH.mono_measure (Measure.prod_mono le_rfl hn)
  refine ⟨hip.integral_prod_left.sub hin.integral_prod_left,hH.integral_prod_right,?_⟩
  change (∫ x, (∫ r, H (x,r) ∂ν.toJordanDecomposition.posPart)-
    (∫ r, H (x,r) ∂ν.toJordanDecomposition.negPart) ∂μ) = _
  rw [integral_sub hip.integral_prod_left hin.integral_prod_left,
    integral_integral_swap (f := fun x r => H (x,r)) hip,
    integral_integral_swap (f := fun x r => H (x,r)) hin]
  rfl

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.signed_integral_fubini
