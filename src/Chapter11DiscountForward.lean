import Chapter11DiscountAssociationDiagram
import Chapter11BankDiscountData
import Chapter4FinitePathLift

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- Assemble the printed forward discounting proof for measurable holdings.
 All auxiliary quantities are actual integrals on the established domains;
 no differential identity or associativity identity is taken as a premise. -/
theorem discounted_self_financing_forward
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (S B D V A M AH MH E AD MD JStock DAH DE HAD HJ Z W DEBank HSDiscount G : ClosedTime T → Ω → ℝ)
    (H η r : Ω × ℝ → ℝ)
    (hH : ∀ w,Measurable (fun s => H (w,s))) (hη : ∀ w,Measurable (fun s => η (w,s)))
    (hSm : ∀ w,Measurable (fun s => S (realTimeClamp s) w))
    (hD : AdaptedLocalVariationWitness F D)
    (hDc : ∀ w t,t<⊤ → ContinuousAt (fun s => D s w) t)
    (hM : LocalMProcessWitness P F M) (hMD : LocalMProcessWitness P F MD)
    (hW : LocalMProcessWitness P F W)
    (hV : SemimartingaleDecomposition P F V (fun t w => V ⊥ w+AH t w+E t w) MH)
    (hSD : SemimartingaleDecomposition P F (fun t w => S t w*D t w)
      (fun t w => S ⊥ w*D ⊥ w+AD t w+JStock t w) MD)
    (hAH : VariationIntegralFormula P c hc A H AH)
    (hAD : VariationIntegralFormula P c hc A (fun z => D (realTimeClamp z.2) z.1) AD)
    (hDAH : VariationIntegralFormula P c hc AH (fun z => D (realTimeClamp z.2) z.1) DAH)
    (hDE : VariationIntegralFormula P c hc E (fun z => D (realTimeClamp z.2) z.1) DE)
    (hHAD : VariationIntegralFormula P c hc AD H HAD)
    (hHJ : VariationIntegralFormula P c hc JStock H HJ)
    (hZ : VariationIntegralFormula P c hc A (fun z => H z*D (realTimeClamp z.2) z.1) Z)
    (hMHI : ItoCovarianceFormula P F M H MH)
    (hMDI : ItoCovarianceFormula P F M (fun z => D (realTimeClamp z.2) z.1) MD)
    (hWI : ItoCovarianceFormula P F M (fun z => H z*D (realTimeClamp z.2) z.1) W)
    (hE : VariationIntegralFormula P c hc B η E)
    (hDEBank : VariationIntegralFormula P c hc B (fun z => D (realTimeClamp z.2) z.1*η z) DEBank)
    (hJStock : VariationIntegralFormula P c hc D (fun z => S (realTimeClamp z.2) z.1) JStock)
    (hHSDiscount : VariationIntegralFormula P c hc D (fun z => H z*S (realTimeClamp z.2) z.1) HSDiscount)
    (hG : SemimartingaleIntegralFormula P F c hc
      (fun t w => S ⊥ w*D ⊥ w+AD t w+JStock t w) MD H G)
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T)
    (hbank : BankDiscountData P B D r H η (fun z => S (realTimeClamp z.2) z.1)
      (fun z => V (realTimeClamp z.2) z.1) d) :
    (fun w => V (realTimeClamp d) w*D (realTimeClamp d) w)=ᵐ[P]
      fun w => V ⊥ w*D ⊥ w+G (realTimeClamp d) w := by
  obtain ⟨K,L,hKL,hK,hL⟩ := hG
  obtain ⟨I,J,N,hIN,hI,hJ,hN,hprod⟩ := discount_product_constructed P hT F hF hle hnull
    V _ MH D hV hD hDc c hc hcm hcT hcc
  have hDm w := open_path_real_measurable _ (hDc w)
  have hdiagram := discount_stock_association_diagram P hT F hF hle hnull c hc hcT hcc
    A M AH MH AD MD DAH N HAD L Z W H (fun z => D (realTimeClamp z.2) z.1)
    hH hDm hM hV.martingale hMD hIN.martingale hKL.martingale hW
    hAH hAD hDAH hHAD hZ hMHI hMDI hN hL hWI
  have hIV := variation_integral_sum_increments P c hc hcT hcc
    (fun t w => V ⊥ w+AH t w+E t w) AH E DAH DE I (fun z => D (realTimeClamp z.2) z.1)
    (ae_of_all _ fun w s t _ _ => by ring) hDAH hDE hI
  have hKS := variation_integral_sum_increments P c hc hcT hcc
    (fun t w => S ⊥ w*D ⊥ w+AD t w+JStock t w) AD JStock HAD HJ K H
    (ae_of_all _ fun w s t _ _ => by ring) hHAD hHJ hK
  have hDEeq := variation_integral_associativity P c hc hcT hcc B E DE DEBank
    (fun z => D (realTimeClamp z.2) z.1) η hDm hη hE hDE hDEBank
  have hHJeq := variation_integral_associativity P c hc hcT hcc D JStock HJ HSDiscount
    H (fun z => S (realTimeClamp z.2) z.1) hH hSm hJStock hHJ hHSDiscount
  have hcancel := hbank.cancel P B D r H η _ _ d c hc hcT hcc hd hdT DEBank J HSDiscount hDEBank hJ hHSDiscount
  have hdt : realTimeClamp (T:=T) d<⊤ := real_time_below d hd hdT
  filter_upwards [hprod,hdiagram,hIV,hKS,hDEeq,hHJeq,hcancel] with w hp hdg hiv hks hde hhj hcan
  have hp' := hp _ hdt
  have hdg' := hdg _ hdt
  have hi' := hiv _ hdt
  have hk' := hks _ hdt
  have he' := hde _ hdt
  have hj' := hhj _ hdt
  rw [hKL.decomposition _ hdt w]
  linarith

end Asakura.Chapter11
