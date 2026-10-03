import Chapter3VariationChainRule

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-- Values outside the original time domain do not affect the signed
variation integral. The support is derived from its existing definition. -/
theorem variation_integral_integrand_congr_on_domain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)]
    (A I : ClosedTime T → Ω → ℝ) (H K : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hcT : ∀ n, (c n:EReal) < T)
    (hI : VariationIntegralFormula P c hc A H I)
    (he : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → (r:EReal) < T → H (ω,r) = K (ω,r)) :
    VariationIntegralFormula P c hc A K I := by
  intro n
  obtain ⟨ν,hs,hν,hi,hform⟩ := hI n
  refine ⟨ν,hs,hν,?_,?_⟩
  · filter_upwards [hs,hi,he] with ω hsω hiω heω
    apply hiω.congr
    filter_upwards [hsω] with r hr
    exact heω r hr.1.le ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
  · filter_upwards [hs,hform,he] with ω hsω hfω heω
    intro t
    rw [hfω t]
    apply signedIntegralRaw_congr_ae (ν ω).totalVariation (ν ω) 1 (by norm_num) (by simp)
    filter_upwards [hsω] with r hr
    by_cases ht : r ∈ Iic (finitePrefixTime (c n) (hc n) t).val
    · simp only [indicator_of_mem ht]
      exact heω r hr.1.le ((EReal.coe_le_coe hr.2).trans_lt (hcT n))
    · simp only [indicator_of_notMem ht]

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.variation_integral_integrand_congr_on_domain
