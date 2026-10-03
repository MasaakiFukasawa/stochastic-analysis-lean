import Chapter2SemimartingaleAssociativity
import Chapter2VariationAssociativityProgressive

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Associativity on the actual integral domains, without continuity of
 either integrand. Existence of the three integrals is expressed by their
 Stieltjes and Ito formulas, not by an assumed associativity identity. -/
theorem general_semimartingale_associativity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (A M A1 M1 Y Z : ClosedTime T → Ω → ℝ)
    (G H : Ω × ℝ → ℝ)
    (hM : LocalMProcessWitness P F M) (hM1 : LocalMProcessWitness P F M1)
    (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hA1 : VariationIntegralFormula P c hc A G A1)
    (hI1 : ItoCovarianceFormula P F M G M1)
    (hY : SemimartingaleIntegralFormula P F c hc A1 M1 H Y)
    (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => H z*G z) Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → Y t w=Z t w := by
  obtain ⟨A2,M2,hD2,hA2,hM2⟩ := hY
  obtain ⟨A3,M3,hD3,hA3,hM3⟩ := hZ
  have ha := variation_integral_associativity P c hc hcT hcc A A1 A2 A3 H G hHm hGm hA1 hA2 hA3
  have hm := ito_integral_associativity P hT F hF hle hnull M M1 M2 M3 G H
    hM hM1 hD2.martingale hD3.martingale hGm hHm hI1 hM2 hM3
  filter_upwards [ha,hm] with w hwA hwM
  intro t ht
  rw [hD2.decomposition t ht w,hD3.decomposition t ht w,hwA t ht,hwM t ht]

end Asakura.Chapter11
