import Chapter12SignedDensityProductIntegrable
import Chapter2ItoAssociativity

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Composition constructs the product-integrand Ito formula, with its
integrability derived from exact total variation of the covariance density. -/
theorem ito_forward_associativity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0≤T)]
    (F : ClosedTime T → MeasurableSpace Ω)
    (X Y Z : ClosedTime T → Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (hY : LocalMProcessWitness P F Y)
    (hG : ∀ w,Measurable (fun t => G (w,t)))
    (hH : ∀ w,Measurable (fun t => H (w,t)))
    (hy : ItoCovarianceFormula P F X G Y)
    (hz : ItoCovarianceFormula P F Y H Z) :
    ItoCovarianceFormula P F X (fun z => H z*G z) Z := by
  intro N C hN hC
  obtain ⟨D,hD,hDp⟩ := hy.finite_process_formula P F X Y G hY hG N C hN hC
  obtain ⟨E,hE,hEp⟩ := hz N D hN hD
  refine ⟨E,hE,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hDp d hd0 hdT
  obtain ⟨κ,hκ,hκ0,hκi,hκE⟩ := hEp d hd0 hdT
  have hdata : ∀ᵐ w ∂P,Integrable (fun t => H (w,t)*G (w,t)) (ν w).totalVariation ∧
      signedIntegralRaw (κ w) (fun t => H (w,t))=
        signedIntegralRaw (ν w) (fun t => H (w,t)*G (w,t)) := by
    filter_upwards [hν0,hνi,hνD,hκ0,hκi] with w hn0 hni hnD hk0 hki
    have hνr : ν w=(ν w).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun t => C (realTimeClamp t) w)
        d d hd0 le_rfl (ν w) (ν w) hn0 hn0
      all_goals
        intro a b ha hab
        simpa only [real_time_clamp_mono.map_min] using hν w a b ha hab
    have hinc : ∀ a b,0≤a → a≤b → κ w (Ioc a b)=
        signedCumulative (ν w) (fun t => G (w,t)) (min b d)-
        signedCumulative (ν w) (fun t => G (w,t)) (min a d) := by
      intro a b ha hab
      have ha' := hnD (min a d) ⟨le_min ha hd0,min_le_right _ _⟩
      have hb' := hnD (min b d) ⟨le_min (ha.trans hab) hd0,min_le_right _ _⟩
      simp only [real_time_clamp_mono.map_min] at ha' hb'
      rw [hκ w a b ha hab,ha',hb']
    have he := signed_cumulative_density_identification (ν w) (κ w) _ (hG w) hni d hn0 hk0 hνr hinc
    have hprod : Integrable (fun t => H (w,t)*G (w,t)) (ν w).totalVariation := by
      rw [he] at hki
      exact signed_density_product_integrable (ν w) _ _ (hG w) (hH w) hni hki
    exact ⟨hprod,signed_iterated_integral_of_cumulative (ν w) (κ w) _ _
      (hG w) (hH w) hni hki hprod d hn0 hk0 hνr hinc⟩
  refine ⟨ν,hν,hν0,hdata.mono (fun _ h => h.1),?_⟩
  filter_upwards [hκE,hdata] with w hw hd
  exact hw.trans hd.2

end Asakura.Chapter12
#print axioms Asakura.Chapter12.ito_forward_associativity
