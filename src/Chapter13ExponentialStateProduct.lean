import Chapter3VariationIntegrandCongruence
import Chapter13ExponentialModel
import Chapter4C1ClockVariation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter13
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter11
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Exponential rescaling of the actual state semimartingale. The stochastic
integral is constructed, not supplied as an assumption. The remaining two
terms are Stieltjes integrals identified by their time densities. -/
theorem exponential_state_product {Ω:Type*} {m:MeasurableSpace Ω}
    (P:Measure Ω) [IsProbabilityMeasure P] {T:EReal} [Fact (0≤T)] (hT:0<T)
    (F:ClosedTime T → MeasurableSpace Ω) (hF:Monotone F) (hle:∀t,F t≤m)
    (hnull:∀t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X A M K:ClosedTime T → Ω → ℝ) (hX:SemimartingaleDecomposition P F X A M)
    (hKa:∀t,t<⊤ → Measurable[F t] (K t))
    (hclock:∀w (r:ℝ),0≤r → (r:EReal)<T → K (realTimeClamp r) w=r)
    (a:ℝ) (c:ℕ → ℝ) (hc:∀n,0≤c n) (hcm:Monotone c) (hcT:∀n,(c n:EReal)<T)
    (hcc:∀t,t<⊤ → ∃n,t<realTimeClamp (T:=T) (c n)) :
    ∃I J N,SemimartingaleDecomposition P F (fun t w => I t w+N t w) I N ∧
      VariationIntegralFormula P c hc A (fun z => Real.exp (-a*z.2)) I ∧
      VariationIntegralFormula P c hc (fun t w => Real.exp (-a*K t w))
        (fun z => X (realTimeClamp z.2) z.1) J ∧
      ItoCovarianceFormula P F M (fun z => Real.exp (-a*z.2)) N ∧
      ∀ᵐw∂P,∀r:ℝ,0≤r → (r:EReal)<T →
        Real.exp (-a*r)*X (realTimeClamp r) w=X ⊥ w+I (realTimeClamp r) w+J (realTimeClamp r) w+N (realTimeClamp r) w := by
  have hv:ContDiff ℝ 1 (fun r:ℝ => Real.exp (-a*r)) := by fun_prop
  have hD:=C1_clock_adapted_variation hT F hF K hKa hclock (fun r => Real.exp (-a*r)) hv
  have hKc:∀w t,t<⊤ → ContinuousAt (fun s => K s w) t := (clock_regular_from_identity K hclock).2
  obtain ⟨I,J,N,hIN,hI,hJ,hN,he⟩:=discount_product_constructed P hT F hF hle hnull X A M
    (fun t w => Real.exp (-a*K t w)) hX hD
    (fun w t ht => hv.continuous.continuousAt.comp (hKc w t ht)) c hc hcm hcT hcc
  have hzero w:K ⊥ w=0 := by
    have hh:=hclock w 0 le_rfl hT
    have hz:realTimeClamp (T:=T) 0=⊥ := Subtype.ext (real_time_clamp_eq 0 le_rfl hT.le)
    simpa only [hz] using hh
  refine ⟨I,J,N,hIN,?_,hJ,?_,?_⟩
  · exact variation_integral_integrand_congr_on_domain P A I _ _ c hc hcT hI
      (ae_of_all _ fun w r hr hrT => by rw [hclock w r hr hrT])
  · exact hN.congr_on_time_domain P F M N _ _ (fun w r hr hrT => by rw [hclock w r hr hrT])
  · filter_upwards [he] with w hw
    intro r hr hrT
    have hh:=hw _ (real_time_below r hr hrT)
    rw [hclock w r hr hrT,hzero,mul_zero,Real.exp_zero,mul_one] at hh
    simpa only [mul_comm] using hh
end Asakura.Chapter13
#print axioms Asakura.Chapter13.exponential_state_product
