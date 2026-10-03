import Chapter10ScalarObservationInverse
import Chapter2VariationAssociativity

open MeasureTheory Set Filter
namespace Asakura.Chapter10
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Associativity with the actual chosen component integrals, on the same
time exhaustion as the observation model. -/
theorem actual_semimartingale_integral_associativity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M Y A1 M1 U Z : HalfClosedTime → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y A1 M1)
    (H G : ℝ → ℝ) (hH : Measurable H) (hG : Measurable G)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ k,t<realTimeClamp (c k))
    (hA1 : VariationIntegralFormula P c hc A (fun z => G z.2) A1)
    (hM1 : ItoCovarianceFormula P F M (fun z => G z.2) M1)
    (hU : SemimartingaleIntegralFormula P F c hc A1 M1 (fun z => H z.2) U)
    (hZ : SemimartingaleIntegralFormula P F c hc A M (fun z => H z.2*G z.2) Z) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → U t w=Z t w := by
  obtain ⟨A2,M2,hU,hA2,hM2⟩ := hU
  obtain ⟨A3,M3,hZ,hA3,hM3⟩ := hZ
  have ha := variation_integral_associativity P c hc hcT hcc A A1 A2 A3
    (fun z => H z.2) (fun z => G z.2) (fun _ => hH) (fun _ => hG) hA1 hA2 hA3
  have hm := ito_integral_associativity P (by simp : (0:EReal)<⊤) F hF hle hnull M M1 M2 M3
    (fun z => G z.2) (fun z => H z.2) hX.martingale hY.martingale hU.martingale hZ.martingale
    (fun _ => hG) (fun _ => hH) hM1 hM2 hM3
  filter_upwards [ha,hm] with w ha hm
  intro t ht
  rw [hU.decomposition t ht w,hZ.decomposition t ht w,ha t ht,hm t ht]

end Asakura.Chapter10
