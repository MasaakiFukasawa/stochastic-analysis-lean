import Chapter2VariationCumulativeIdentification
import Chapter2SignedDensityIdentification

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- Associativity for the actual constructed finite-variation integrals.
The Stieltjes measure of G·A is identified as G dA from its increments;
the signed change-of-density theorem then gives H·(G·A)=(HG)·A. -/
theorem variation_integral_associativity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0 ≤ T)] (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hcT : ∀ n, (c n:EReal) < T)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < realTimeClamp (T := T) (c n))
    (A J K L : ClosedTime T → Ω → ℝ) (H G : Ω × ℝ → ℝ)
    (hHm : ∀ ω, Measurable (fun r => H (ω,r)))
    (hGm : ∀ ω, Measurable (fun r => G (ω,r)))
    (hJ : VariationIntegralFormula P c hc A G J)
    (hK : VariationIntegralFormula P c hc J H K)
    (hL : VariationIntegralFormula P c hc A (fun z => H z*G z) L) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → K t ω = L t ω := by
  have he n : ∀ᵐ ω ∂P, ∀ t,
      K (min (realTimeClamp (c n)) t) ω = L (min (realTimeClamp (c n)) t) ω := by
    obtain ⟨ξ,hsξ,hξ,hiG,heJ⟩ := hJ n
    obtain ⟨η,_,hη,hiH,heK⟩ := hK n
    obtain ⟨ρ,_,hρ,hiHG,heL⟩ := hL n
    filter_upwards [hsξ,hξ,hiG,heJ,hη,hiH,heK,hρ,hiHG,heL] with
      ω hsω hξω hiGω heJω hηω hiHω heKω hρω hiHGω heLω
    have heξ : ξ ω = ρ ω := signed_measure_ext_Ioc _ _
      (fun a b hab => (hξω a b hab.le).trans (hρω a b hab.le).symm)
    rw [← heξ] at hiHGω heLω
    have hJcum := variation_sample_cumulative_identification (c n) (hc n) (hcT n).le
      (ξ ω) (fun r => G (ω,r)) (fun t => J t ω) hsω heJω
    have heη : η ω = signedWeighted (ξ ω) (fun r => G (ω,r)) := by
      apply signed_measure_ext_Ioc
      intro a b hab
      rw [hηω a b hab.le,hJcum b,hJcum a,
        signed_cumulative_increment (ξ ω) _ hiGω a b hab.le,
        signed_weighted_apply (ξ ω) _ hiGω (Ioc a b) measurableSet_Ioc]
    intro t
    rw [heKω t,heLω t]
    let B := Iic (finitePrefixTime (c n) (hc n) t).val
    have hprod : (fun r => (B.indicator (fun r => H (ω,r))) r*G (ω,r)) =
        B.indicator (fun r => H (ω,r)*G (ω,r)) := by
      funext r
      by_cases hr : r ∈ B <;> simp [hr]
    change signedIntegralRaw (η ω) (B.indicator (fun r => H (ω,r))) =
      signedIntegralRaw (ξ ω) (B.indicator (fun r => H (ω,r)*G (ω,r)))
    rw [← hprod]
    apply signed_density_integral (ξ ω) (η ω) _ _ (hGm ω) ((hHm ω).indicator measurableSet_Iic)
      hiGω (hiHω.indicator measurableSet_Iic)
    · rw [hprod]
      exact hiHGω.indicator measurableSet_Iic
    · intro C hC
      rw [heη,signed_weighted_apply (ξ ω) _ hiGω C hC]
  filter_upwards [ae_all_iff.mpr he] with ω hω
  intro t ht
  obtain ⟨n,hn⟩ := hcc t ht
  simpa only [min_eq_right hn.le] using hω n t

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.variation_integral_associativity
