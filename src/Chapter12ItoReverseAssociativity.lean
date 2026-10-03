import Chapter12SignedWeightedIntegrability
import Chapter2ItoAssociativity
import Chapter2ContinuousIntegrand

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Construct the outer Ito integral by its actual covariance measures.
The output integral is not a hypothesis. -/
theorem ito_reverse_associativity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnull : ∀ t N,MeasurableSet[m] N → P N=0 → MeasurableSet[F t] N)
    (X Y W : ClosedTime T → Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hW : LocalMProcessWitness P F W)
    (hG : ∀ ω,Measurable (fun r => G (ω,r)))
    (hH : ∀ ω,Measurable (fun r => H (ω,r)))
    (hy : ItoCovarianceFormula P F X G Y)
    (hw : ItoCovarianceFormula P F X (fun z => H z*G z) W) :
    ItoCovarianceFormula P F Y H W := by
  obtain ⟨J,hJ,hJI⟩ := continuous_adapted_ito_exists P hT F hF hle hnull Y hY
    (fun _ => 1) (fun _ _ _ => measurable_const) (fun _ _ _ _ => continuousOn_const)
  intro N C0 hN hC0
  obtain ⟨C,hC⟩ := local_covariance_witness_exists P F hF hle hnull X N hX hN
  obtain ⟨D,hD,hDp⟩ := hy.finite_process_formula P F X Y G hY hG N C hN hC
  obtain ⟨K,hK,hKp⟩ := hw N C hN hC
  obtain ⟨E,hE,hEp⟩ := hJI N C0 hN hC0
  have hDC := hD.unique P F hF hle hC0
  refine ⟨K,hK,?_⟩
  intro d hd0 hdT
  obtain ⟨ν,hν,hν0,hνi,hνD⟩ := hDp d hd0 hdT
  obtain ⟨κ,hκ,hκ0,_,_⟩ := hEp d hd0 hdT
  obtain ⟨ξ,hξ,hξ0,hξi,hξK⟩ := hKp d hd0 hdT
  have hdata : ∀ᵐ ω ∂P, Integrable (fun r => H (ω,r)) (κ ω).totalVariation ∧
      signedIntegralRaw (κ ω) (fun r => H (ω,r)) =
        signedIntegralRaw (ν ω) (fun r => H (ω,r)*G (ω,r)) := by
    filter_upwards [hν0,hνi,hνD,hκ0,hξ0,hξi,hDC]
      with ω hn0 hni hnD hk0 hx0 hxi hdc
    have heq : ξ ω = ν ω := signed_measure_ext_positive_Ioc _ _ hx0 hn0
      (fun a b ha hab => (hξ ω a b ha hab).trans (hν ω a b ha hab).symm)
    rw [heq] at hxi
    have hνr : ν ω = (ν ω).restrict (Iic d) := by
      apply signed_stopped_interval_consistency (fun r => C (realTimeClamp r) ω)
        d d hd0 le_rfl (ν ω) (ν ω) hn0 hn0
      all_goals
        intro a b ha hab
        simpa only [real_time_clamp_mono.map_min] using hν ω a b ha hab
    have hinc : ∀ a b,0≤a → a≤b → κ ω (Ioc a b)=
        signedCumulative (ν ω) (fun r => G (ω,r)) (min b d)-
        signedCumulative (ν ω) (fun r => G (ω,r)) (min a d) := by
      intro a b ha hab
      have hbelow r (hr : r∈Icc 0 d) : realTimeClamp (T:=T) r < ⊤ := by
        change (realTimeClamp r:EReal)<T
        rw [real_time_clamp_eq r hr.1 ((EReal.coe_le_coe hr.2).trans hdT.le)]
        exact (EReal.coe_le_coe hr.2).trans_lt hdT
      have ha' : min a d∈Icc 0 d := ⟨le_min ha hd0,min_le_right _ _⟩
      have hb' : min b d∈Icc 0 d := ⟨le_min (ha.trans hab) hd0,min_le_right _ _⟩
      rw [hκ ω a b ha hab,← real_time_clamp_mono.map_min,← real_time_clamp_mono.map_min,
        ← hdc _ (hbelow _ hb'),← hdc _ (hbelow _ ha'),hnD _ hb',hnD _ ha']
    have he := signed_cumulative_density_identification (ν ω) (κ ω) _ (hG ω) hni d hn0 hk0 hνr hinc
    have hi : Integrable (fun r => H (ω,r)) (κ ω).totalVariation := by
      rw [he]
      exact signed_weighted_integrable (ν ω) _ _ (hG ω) (hH ω) hni hxi
    exact ⟨hi,signed_iterated_integral_of_cumulative (ν ω) (κ ω) _ _
      (hG ω) (hH ω) hni hi hxi d hn0 hk0 hνr hinc⟩
  refine ⟨κ,hκ,hκ0,hdata.mono (fun _ h => h.1),?_⟩
  filter_upwards [hdata,hν0,hξ0,hξK] with ω hdata hn0 hx0 hxK
  have heq : ξ ω = ν ω := signed_measure_ext_positive_Ioc _ _ hx0 hn0
    (fun a b ha hab => (hξ ω a b ha hab).trans (hν ω a b ha hab).symm)
  rw [hxK,heq,hdata.2]

end Asakura.Chapter12
#print axioms Asakura.Chapter12.ito_reverse_associativity
