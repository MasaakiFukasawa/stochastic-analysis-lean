import Chapter11BankCancellation

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter5

/-- Local data of the bank account and its reciprocal, obtained from the
 integrable short rate. Holdings only require the displayed L1 domains. -/
structure BankDiscountData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)] (B D : ClosedTime T → Ω → ℝ)
    (r H η S V : Ω × ℝ → ℝ) (d : ℝ) : Prop where
  bank : ∀ᵐ w ∂P,∀ t∈Icc 0 d,B (realTimeClamp t) w=B ⊥ w+∫ u in 0..t,r (w,u)*B (realTimeClamp u) w
  discount : ∀ᵐ w ∂P,∀ t∈Icc 0 d,D (realTimeClamp t) w=D ⊥ w+∫ u in 0..t,-r (w,u)*D (realTimeClamp u) w
  bank_measurable : ∀ w,Measurable (fun t => r (w,t)*B (realTimeClamp t) w)
  discount_measurable : ∀ w,Measurable (fun t => -r (w,t)*D (realTimeClamp t) w)
  bank_integrable : ∀ᵐ w ∂P,IntervalIntegrable (fun t => r (w,t)*B (realTimeClamp t) w) volume 0 d
  discount_integrable : ∀ᵐ w ∂P,IntervalIntegrable (fun t => -r (w,t)*D (realTimeClamp t) w) volume 0 d
  bank_holdings_measurable : ∀ w,Measurable (fun t => D (realTimeClamp t) w*η (w,t))
  wealth_measurable : ∀ w,Measurable (fun t => V (w,t))
  stock_holdings_measurable : ∀ w,Measurable (fun t => H (w,t)*S (w,t))
  bank_holdings_integrable : ∀ᵐ w ∂P,IntervalIntegrable (fun t => (D (realTimeClamp t) w*η (w,t))*(r (w,t)*B (realTimeClamp t) w)) volume 0 d
  wealth_integrable : ∀ᵐ w ∂P,IntervalIntegrable (fun t => V (w,t)*(-r (w,t)*D (realTimeClamp t) w)) volume 0 d
  stock_holdings_integrable : ∀ᵐ w ∂P,IntervalIntegrable (fun t => (H (w,t)*S (w,t))*(-r (w,t)*D (realTimeClamp t) w)) volume 0 d
  balance : ∀ᵐ w ∂P,∀ t∈Icc 0 d,V (w,t)=H (w,t)*S (w,t)+η (w,t)*B (realTimeClamp t) w

lemma BankDiscountData.cancel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)]
    (B D : ClosedTime T → Ω → ℝ) (r H η S V : Ω × ℝ → ℝ) (d : ℝ)
    (h : BankDiscountData P B D r H η S V d)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n)) (hd : 0≤d) (hdT : (d:EReal)<T)
    (I J K : ClosedTime T → Ω → ℝ)
    (hI : VariationIntegralFormula P c hc B (fun z => D (realTimeClamp z.2) z.1*η z) I)
    (hJ : VariationIntegralFormula P c hc D V J)
    (hK : VariationIntegralFormula P c hc D (fun z => H z*S z) K) :
    (fun w => I (realTimeClamp d) w+J (realTimeClamp d) w)=ᵐ[P] K (realTimeClamp d) :=
  bank_discount_drift_cancellation P B D I J K r H η S V c hc hcT hcc d hd hdT
    h.bank h.discount h.bank_measurable h.discount_measurable h.bank_integrable h.discount_integrable
    h.bank_holdings_measurable h.wealth_measurable h.stock_holdings_measurable
    h.bank_holdings_integrable h.wealth_integrable h.stock_holdings_integrable h.balance hI hJ hK

end Asakura.Chapter11
