import Chapter3ProductFormula

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's self-financing criterion when the holdings themselves
are continuous semimartingales, derived from both actual product formulas. -/
theorem self_financing_product_criterion {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (S H B η AS AH Aη MS MH Mη C IS IH IB Iη : ClosedTime T → Ω → ℝ)
    (hS : SemimartingaleDecomposition P F S AS MS)
    (hH : SemimartingaleDecomposition P F H AH MH)
    (hB : SemimartingaleDecomposition P F B B (fun _ _ => 0))
    (hη : SemimartingaleDecomposition P F η Aη Mη)
    (hC : LocalCovarianceWitness P F MS MH C)
    (c : ℕ → ℝ) (hc : ∀ k,0≤c k) (hcT : ∀ k,(c k:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ k,t<realTimeClamp (T:=T) (c k))
    (hIS : SemimartingaleIntegralFormula P F c hc AS MS (fun z => H (realTimeClamp z.2) z.1) IS)
    (hIH : SemimartingaleIntegralFormula P F c hc AH MH (fun z => S (realTimeClamp z.2) z.1) IH)
    (hIB : SemimartingaleIntegralFormula P F c hc B (fun _ _ => 0) (fun z => η (realTimeClamp z.2) z.1) IB)
    (hIη : SemimartingaleIntegralFormula P F c hc Aη Mη (fun z => B (realTimeClamp z.2) z.1) Iη) :
    ∀ᵐ w ∂P,∀ t,t<⊤ →
      (H t w*S t w+η t w*B t w=H ⊥ w*S ⊥ w+η ⊥ w*B ⊥ w+IS t w+IB t w ↔
        IH t w+Iη t w+C t w=0) := by
  have hz : LocalCovarianceWitness P F (fun _ _ => 0) Mη (fun _ _ => 0) := by
    constructor
    · convert hB.martingale using 1 <;> simp
    · convert hB.variation.toPathwise.smul F 0 using 1 <;> simp
  have hs := semimartingale_product_formula P hT F hF hle hnull S H AS AH MS MH C IS IH
    hS hH hC c hc hcT hcc hIS hIH
  have hb := semimartingale_product_formula P hT F hF hle hnull B η B Aη (fun _ _ => 0) Mη
    (fun _ _ => 0) IB Iη hB hη hz c hc hcT hcc hIB hIη
  filter_upwards [hs,hb] with w hs hb
  intro t ht
  have hh := hs t ht
  have hh' := hb t ht
  constructor <;> intro h <;> nlinarith only [hh,hh',h]

end Asakura.Chapter11
