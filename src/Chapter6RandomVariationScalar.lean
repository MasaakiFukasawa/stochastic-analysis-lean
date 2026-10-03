import Chapter3VariationIntegratorCongruence
import Chapter2SignedDensityIntegral
import Chapter2ContinuousVariationAssociativity

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Scalar multiplication in the actual signed Stieltjes integral. -/
theorem variation_integrand_random_scalar
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n,0 ≤ c n)
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ) (a : Ω → ℝ)
    (hI : VariationIntegralFormula P c hc A H I) :
    VariationIntegralFormula P c hc A (fun z => a z.1*H z) (fun t w => a w*I t w) := by
  intro n
  obtain ⟨ν,hs,hν,hi,he⟩ := hI n
  refine ⟨ν,hs,hν,hi.mono (fun w hw => hw.const_mul (a w)),?_⟩
  filter_upwards [he] with w hw
  intro t
  rw [hw t]
  unfold signedCumulative
  have hind (r : ℝ) : (Iic (finitePrefixTime (c n) (hc n) t).val).indicator
      (fun r => a w*H (w,r)) r =
      a w*((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => H (w,r)) r) := by
    by_cases hr : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val <;> simp [hr]
  change a w*signedIntegralRaw (ν w) _ = signedIntegralRaw (ν w) ((Iic _).indicator (fun r => a w*H (w,r)))
  rw [funext hind]
  exact (signed_integral_const_mul (ν w) _ (a w)).symm


end Asakura.Chapter6
