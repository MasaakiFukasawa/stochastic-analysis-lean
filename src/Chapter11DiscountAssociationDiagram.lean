import Chapter11GeneralAssociativity
import Chapter11VariationSumIncrements
import Chapter11DiscountProduct

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

/-- The two orders of integration in the discounting proof give the same
 stock term. Every edge is an actual Stieltjes or Ito integral. The holdings
 are measurable, not assumed continuous. -/
theorem discount_stock_association_diagram
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (A M AH MH AD MD DAH DAM HAD HAM Z W : ClosedTime T → Ω → ℝ)
    (H D : Ω × ℝ → ℝ)
    (hH : ∀ w,Measurable (fun s => H (w,s))) (hD : ∀ w,Measurable (fun s => D (w,s)))
    (hM : LocalMProcessWitness P F M) (hMH : LocalMProcessWitness P F MH)
    (hMD : LocalMProcessWitness P F MD) (hDAM : LocalMProcessWitness P F DAM)
    (hHAM : LocalMProcessWitness P F HAM) (hW : LocalMProcessWitness P F W)
    (hAH : VariationIntegralFormula P c hc A H AH)
    (hAD : VariationIntegralFormula P c hc A D AD)
    (hDAH : VariationIntegralFormula P c hc AH D DAH)
    (hHAD : VariationIntegralFormula P c hc AD H HAD)
    (hZ : VariationIntegralFormula P c hc A (fun z => H z*D z) Z)
    (hMHI : ItoCovarianceFormula P F M H MH)
    (hMDI : ItoCovarianceFormula P F M D MD)
    (hDAMI : ItoCovarianceFormula P F MH D DAM)
    (hHAMI : ItoCovarianceFormula P F MD H HAM)
    (hWI : ItoCovarianceFormula P F M (fun z => H z*D z) W) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → DAH t w=HAD t w ∧ DAM t w=HAM t w := by
  have hZ' : VariationIntegralFormula P c hc A (fun z => D z*H z) Z := by
    convert hZ using 1
    funext z;ring
  have hW' : ItoCovarianceFormula P F M (fun z => D z*H z) W := by
    convert hWI using 1
    funext z;ring
  have h1 := variation_integral_associativity P c hc hcT hcc A AH DAH Z D H hD hH hAH hDAH hZ'
  have h2 := variation_integral_associativity P c hc hcT hcc A AD HAD Z H D hH hD hAD hHAD hZ
  have h3 := ito_integral_associativity P hT F hF hle hnull M MH DAM W H D hM hMH hDAM hW hH hD hMHI hDAMI hW'
  have h4 := ito_integral_associativity P hT F hF hle hnull M MD HAM W D H hM hMD hHAM hW hD hH hMDI hHAMI hWI
  filter_upwards [h1,h2,h3,h4] with w h1 h2 h3 h4
  intro t ht
  exact ⟨(h1 t ht).trans (h2 t ht).symm,(h3 t ht).trans (h4 t ht).symm⟩

end Asakura.Chapter11
