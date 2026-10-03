import Chapter12DiscountProductVariation
import Chapter12ConstantIntegrator
import Chapter12ItoForwardAssociativity
import Chapter12ItoReverseAssociativity
import Chapter12VariationReverseAssociativity
import Chapter6VariationAdd
import Chapter3IncreasingAdaptedVariation

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

/-- Construct original stock gains from the discounted martingale hedge.
Only the bank integral on its actual integrability domain is supplied;
all stock integrals are built by product and composition formulas. -/
theorem discounted_replication_original_gains {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnull : ∀ t A,MeasurableSet[m] A → P A=0 → MeasurableSet[F t] A)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcm : Monotone c) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (Y N B E : ClosedTime T → Ω → ℝ) (x v : ℝ) (H η : Ω × ℝ → ℝ)
    (hY : LocalMProcessWitness P F Y) (hN : LocalMProcessWitness P F N)
    (hH : ∀ w,Measurable (fun t => H (w,t)))
    (hNI : ItoCovarianceFormula P F Y H N)
    (hB : AdaptedLocalVariationWitness F B) (hBc : ∀ w t,t<⊤ → ContinuousAt (fun s => B s w) t)
    (hE : AdaptedLocalVariationWitness F E) (hEc : ∀ w t,t<⊤ → ContinuousAt (fun s => E s w) t)
    (hEI : VariationIntegralFormula P c hc B η E)
    (hbal : ∀ᵐ w ∂P,∀ (t : ℝ),0≤t → (t:EReal)<T →
      v+N (realTimeClamp t) w=H (w,t)*(x+Y (realTimeClamp t) w)+η (w,t)) :
    ∃ A M G : ClosedTime T → Ω → ℝ,
      AdaptedLocalVariationWitness F A ∧ LocalMProcessWitness P F M ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (x+Y t w)*B t w=(x+Y ⊥ w)*B ⊥ w+A t w+M t w) ∧
      SemimartingaleIntegralFormula P F c hc A M H G ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (v+N t w)*B t w=(v+N ⊥ w)*B ⊥ w+G t w+E t w) := by
  have hconst (a : ℝ) : AdaptedLocalVariationWitness F (fun _ _ => a) :=
    continuous_increasing_adapted_variation hT F hF _ (fun _ _ => measurable_const)
      (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  have hS : SemimartingaleDecomposition P F (fun t w => x+Y t w) (fun _ _ => x) Y :=
    ⟨hconst x,hY,fun w t ht => continuousAt_const.add (hY.path P F w t ht),fun _ _ _ => rfl⟩
  have hU : SemimartingaleDecomposition P F (fun t w => v+N t w) (fun _ _ => v) N :=
    ⟨hconst v,hN,fun w t ht => continuousAt_const.add (hN.path P F w t ht),fun _ _ _ => rfl⟩
  obtain ⟨IS,JS,MS,hIMS,hJS,hJSc,hIS,hJSI,hMSI,hPS⟩ :=
    discount_product_with_variation P hT F hF hle hnull _ _ Y B hS hB hBc c hc hcm hcT hcc
  obtain ⟨IU,JU,MU,hIMU,hJU,hJUc,hIU,hJUI,hMUI,hPU⟩ :=
    discount_product_with_variation P hT F hF hle hnull _ _ N B hU hB hBc c hc hcm hcT hcc
  have hIS0 := hIS.unique P c hc hcc _ IS (fun _ _ => 0) _
    (constant_integrator_formula P c hc (fun _ => x) _)
  have hIU0 := hIU.unique P c hc hcc _ IU (fun _ _ => 0) _
    (constant_integrator_formula P c hc (fun _ => v) _)
  have hBm w := open_path_real_measurable _ (hBc w)
  have hSd w : Measurable (fun t => x+Y (realTimeClamp t) w) :=
    measurable_const.add (open_path_real_measurable _ (hY.path P F w))
  have hfwd := ito_forward_associativity P F Y N MU H (fun z => B (realTimeClamp z.2) z.1)
    hN hH hBm hNI hMUI
  have hfwd' : ItoCovarianceFormula P F Y
      (fun z => H z*B (realTimeClamp z.2) z.1) MU := by
    simpa only [mul_comm] using hfwd
  have hstockIto := ito_reverse_associativity P hT F hF hle hnull Y MS MU
    (fun z => B (realTimeClamp z.2) z.1) H hY hIMS.martingale hIMU.martingale hBm hH hMSI hfwd'
  let J := fun t w => JU t w+(-1:ℝ)*E t w
  have hJv : AdaptedLocalVariationWitness F J := hJU.add (hE.smul (-1)) hF
  have hJc w t ht : ContinuousAt (fun s => J s w) t :=
    (hJUc w t ht).add ((hEc w t ht).const_mul (-1))
  have hsum := variation_integrand_add P c hc B JU (fun t w => (-1:ℝ)*E t w)
    (fun z => v+N (realTimeClamp z.2) z.1) (fun z => (-1:ℝ)*η z)
    hJUI (variation_integrand_scalar P c hc B E η (-1) hEI)
  have hprod : VariationIntegralFormula P c hc B
      (fun z => H z*(x+Y (realTimeClamp z.2) z.1)) J := by
    apply variation_integral_integrand_congr_on_domain P B J _ _ c hc hcT hsum
    filter_upwards [hbal] with w hw
    intro t ht htT
    rw [hw t ht htT];ring
  have hstockVar := variation_reverse_associativity P c hc hcT B JS J H
    (fun z => x+Y (realTimeClamp z.2) z.1) hH hSd hJSI hprod
  let G := fun t w => J t w+MU t w
  have hGD : SemimartingaleDecomposition P F G J MU :=
    ⟨hJv,hIMU.martingale,fun w t ht => (hJc w t ht).add (hIMU.martingale.path P F w t ht),fun _ _ _ => rfl⟩
  refine ⟨JS,MS,G,hJS,hIMS.martingale,?_,⟨J,MU,hGD,hstockVar,hstockIto⟩,?_⟩
  · filter_upwards [hPS,hIS0] with w hp hz
    intro t ht
    simpa only [hz t ht,add_zero] using hp t ht
  · filter_upwards [hPU,hIU0] with w hp hz
    intro t ht
    have hh := hp t ht
    rw [hz t ht] at hh
    dsimp only [G,J]
    linarith

end Asakura.Chapter12
#print axioms Asakura.Chapter12.discounted_replication_original_gains
