import Chapter11DiscountAssociationDiagram
import Chapter6VariationAdd
import Chapter4FinitePathLift

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

/-- The reverse implication of the printed discount criterion. Multiplying
 discounted wealth by the bank account and using the actual product and
 associativity formulas produces the original stock and bank gains. -/
theorem discounted_self_financing_reverse
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (Sd B U A M AH MH AB MB JStock BAH HAB HJ Z W HSBank E G : ClosedTime T → Ω → ℝ)
    (H η : Ω × ℝ → ℝ)
    (hH : ∀ w,Measurable (fun s => H (w,s)))
    (hSm : ∀ w,Measurable (fun s => Sd (realTimeClamp s) w))
    (hB : AdaptedLocalVariationWitness F B)
    (hBc : ∀ w t,t<⊤ → ContinuousAt (fun s => B s w) t)
    (hM : LocalMProcessWitness P F M) (hMB : LocalMProcessWitness P F MB)
    (hW : LocalMProcessWitness P F W)
    (hU : SemimartingaleDecomposition P F U (fun t w => U ⊥ w+AH t w) MH)
    (hS : SemimartingaleDecomposition P F (fun t w => Sd t w*B t w)
      (fun t w => Sd ⊥ w*B ⊥ w+AB t w+JStock t w) MB)
    (hAH : VariationIntegralFormula P c hc A H AH)
    (hAB : VariationIntegralFormula P c hc A (fun z => B (realTimeClamp z.2) z.1) AB)
    (hBAH : VariationIntegralFormula P c hc AH (fun z => B (realTimeClamp z.2) z.1) BAH)
    (hHAB : VariationIntegralFormula P c hc AB H HAB)
    (hHJ : VariationIntegralFormula P c hc JStock H HJ)
    (hZ : VariationIntegralFormula P c hc A (fun z => H z*B (realTimeClamp z.2) z.1) Z)
    (hMHI : ItoCovarianceFormula P F M H MH)
    (hMBI : ItoCovarianceFormula P F M (fun z => B (realTimeClamp z.2) z.1) MB)
    (hWI : ItoCovarianceFormula P F M (fun z => H z*B (realTimeClamp z.2) z.1) W)
    (hE : VariationIntegralFormula P c hc B η E)
    (hJStock : VariationIntegralFormula P c hc B (fun z => Sd (realTimeClamp z.2) z.1) JStock)
    (hHSBank : VariationIntegralFormula P c hc B (fun z => H z*Sd (realTimeClamp z.2) z.1) HSBank)
    (hG : SemimartingaleIntegralFormula P F c hc
      (fun t w => Sd ⊥ w*B ⊥ w+AB t w+JStock t w) MB H G)
    (hbalance : ∀ᵐ w ∂P,∀ t : ℝ,0≤t → (t:EReal)<T →
      U (realTimeClamp t) w=H (w,t)*Sd (realTimeClamp t) w+η (w,t)) :
    ∀ᵐ w ∂P,∀ t,t<⊤ → U t w*B t w=U ⊥ w*B ⊥ w+G t w+E t w := by
  obtain ⟨K,L,hKL,hK,hL⟩ := hG
  obtain ⟨I,J,N,hIN,hI,hJ,hN,hprod⟩ := discount_product_constructed P hT F hF hle hnull
    U _ MH B hU hB hBc c hc hcm hcT hcc
  have hBm w := open_path_real_measurable _ (hBc w)
  have hdiagram := discount_stock_association_diagram P hT F hF hle hnull c hc hcT hcc
    A M AH MH AB MB BAH N HAB L Z W H (fun z => B (realTimeClamp z.2) z.1)
    hH hBm hM hU.martingale hMB hIN.martingale hKL.martingale hW
    hAH hAB hBAH hHAB hZ hMHI hMBI hN hL hWI
  have hI' := variation_integral_integrator_increments_congr P AH (fun t w => U ⊥ w+AH t w)
    BAH (fun z => B (realTimeClamp z.2) z.1) c hc hcT hBAH
    (ae_of_all _ fun w s t _ _ => by ring)
  have hIU := VariationIntegralFormula.unique P c hc hcc _ I BAH _ hI hI'
  have hKS := variation_integral_sum_increments P c hc hcT hcc
    (fun t w => Sd ⊥ w*B ⊥ w+AB t w+JStock t w) AB JStock HAB HJ K H
    (ae_of_all _ fun w s t _ _ => by ring) hHAB hHJ hK
  have hHJeq := variation_integral_associativity P c hc hcT hcc B JStock HJ HSBank
    H (fun z => Sd (realTimeClamp z.2) z.1) hH hSm hJStock hHJ hHSBank
  have hsum := variation_integrand_add P c hc B HSBank E
    (fun z => H z*Sd (realTimeClamp z.2) z.1) η hHSBank hE
  have hsum' := variation_integral_integrand_congr_on_domain P B (fun t w => HSBank t w+E t w)
    (fun z => H z*Sd (realTimeClamp z.2) z.1+η z) (fun z => U (realTimeClamp z.2) z.1)
    c hc hcT hsum (hbalance.mono fun w hw s hs hsT => (hw s hs hsT).symm)
  have hJU := VariationIntegralFormula.unique P c hc hcc B J _ _ hJ hsum'
  filter_upwards [hprod,hdiagram,hIU,hKS,hHJeq,hJU] with w hp hdg hi hk hj hju
  intro t ht
  rw [hKL.decomposition t ht w]
  have hp' := hp t ht
  have hdg' := hdg t ht
  have hi' := hi t ht
  have hk' := hk t ht
  have hj' := hj t ht
  have hju' := hju t ht
  linarith

end Asakura.Chapter11
