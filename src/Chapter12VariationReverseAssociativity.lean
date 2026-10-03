import Chapter12SignedWeightedIntegrability
import Chapter2VariationAssociativity

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Construct the outer Stieltjes integral from the product integrand;
its existence is part of the conclusion. -/
theorem variation_reverse_associativity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {T : EReal} [Fact (0≤T)]
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (A J L : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hHm : ∀ w,Measurable (fun t => H (w,t)))
    (hGm : ∀ w,Measurable (fun t => G (w,t)))
    (hJ : VariationIntegralFormula P c hc A G J)
    (hL : VariationIntegralFormula P c hc A (fun z => H z*G z) L) :
    VariationIntegralFormula P c hc J H L := by
  intro n
  obtain ⟨ξ,hsξ,hξ,hiG,heJ⟩ := hJ n
  obtain ⟨ρ,_,hρ,hiHG,heL⟩ := hL n
  let η := fun w => signedWeighted (ξ w) (fun t => G (w,t))
  have heξ : ∀ᵐ w ∂P,ξ w=ρ w := by
    filter_upwards [hξ,hρ] with w hx hr
    exact signed_measure_ext_Ioc _ _ (fun a b hab => (hx a b hab.le).trans (hr a b hab.le).symm)
  have hiH : ∀ᵐ w ∂P,Integrable (fun t => H (w,t)) (η w).totalVariation := by
    filter_upwards [heξ,hiG,hiHG] with w he hg hp
    rw [← he] at hp
    exact signed_weighted_integrable (ξ w) _ _ (hGm w) (hHm w) hg hp
  refine ⟨η,?_,?_,hiH,?_⟩
  · filter_upwards [hsξ,hiG] with w hs hg
    exact (signed_weighted_totalVariation_ac (ξ w) _ hg).ae_le hs
  · filter_upwards [hsξ,hiG,heJ] with w hs hg hj
    have hcumul := variation_sample_cumulative_identification (c n) (hc n) (hcT n).le
      (ξ w) (fun t => G (w,t)) (fun t => J t w) hs hj
    intro a b hab
    rw [hcumul b,hcumul a,signed_cumulative_increment (ξ w) _ hg a b hab]
    exact signed_weighted_apply (ξ w) _ hg (Ioc a b) measurableSet_Ioc
  · filter_upwards [hiG,hiHG,hiH,heξ,heL] with w hg hp hh he hl
    rw [← he] at hp hl
    intro t
    rw [hl t]
    let E := Iic (finitePrefixTime (c n) (hc n) t).val
    have hprod : (fun s => E.indicator (fun r => H (w,r)) s*G (w,s))=
        E.indicator (fun r => H (w,r)*G (w,r)) := by
      funext s
      by_cases hs : s∈E <;> simp [hs]
    change signedIntegralRaw (ξ w) (E.indicator (fun r => H (w,r)*G (w,r)))=
      signedIntegralRaw (η w) (E.indicator (fun r => H (w,r)))
    symm
    rw [← hprod]
    apply signed_density_integral (ξ w) (η w) _ _ (hGm w) ((hHm w).indicator measurableSet_Iic)
      hg (hh.indicator measurableSet_Iic)
    · rw [hprod]
      exact hp.indicator measurableSet_Iic
    · intro C hC
      exact signed_weighted_apply (ξ w) _ hg C hC

end Asakura.Chapter12
#print axioms Asakura.Chapter12.variation_reverse_associativity
