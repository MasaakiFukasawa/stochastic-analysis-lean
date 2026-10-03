import Chapter3VariationIntegrandCongruence
import Chapter2SignedDensityIntegral

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem variation_integral_scalar_multiple
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A I : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hI : VariationIntegralFormula P c hc A H I) (a : ℝ) :
    VariationIntegralFormula P c hc A (fun z => a*H z) (fun t ω => a*I t ω) := by
  intro n
  obtain ⟨ν,hs,hν,hi,hform⟩ := hI n
  refine ⟨ν,hs,hν,hi.mono (fun ω hiω => hiω.const_mul a),?_⟩
  filter_upwards [hform] with ω hω
  intro t
  rw [hω t]
  change a*signedIntegralRaw (ν ω) ((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => H (ω,r))) =
    signedIntegralRaw (ν ω) ((Iic (finitePrefixTime (c n) (hc n) t).val).indicator (fun r => a*H (ω,r)))
  rw [← signed_integral_const_mul]
  congr 1
  funext r
  by_cases hr : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val
  · simp only [indicator_of_mem hr]
  · simp only [indicator_of_notMem hr,mul_zero]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.variation_integral_scalar_multiple
