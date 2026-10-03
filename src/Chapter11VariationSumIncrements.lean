import Chapter11VariationIntegratorAdd
import Chapter3VariationIntegratorCongruence

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2200000

/-- Integrating a sum of increments ignores any random initial constant. -/
theorem variation_integral_sum_increments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)]
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (A B C I J K : ClosedTime T → Ω → ℝ) (H : Ω × ℝ → ℝ)
    (he : ∀ᵐ w ∂P,∀ s t,s<⊤ → t<⊤ → A t w-A s w=(B t w+C t w)-(B s w+C s w))
    (hI : VariationIntegralFormula P c hc B H I)
    (hJ : VariationIntegralFormula P c hc C H J)
    (hK : VariationIntegralFormula P c hc A H K) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → K t w=I t w+J t w := by
  have hh := variation_integral_integrator_increments_congr P _ A _ H c hc hcT
    (variation_integrator_add P c hc B C I J H hI hJ)
    (he.mono fun w hw s t hs ht => (hw s t hs ht).symm)
  exact VariationIntegralFormula.unique P c hc hcc A K _ H hK hh

end Asakura.Chapter11
