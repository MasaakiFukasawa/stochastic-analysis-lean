import Chapter11MarketGainIdentity
import Chapter11InvestmentHoldings

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The investment SDE produces the actual stock-and-bank self-financing
 strategy. The stochastic integral and the variation integrals are identified
 by their formulas, rather than by equating formal differentials. -/
theorem investment_solution_self_financing
{Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (S A MS Bank V G E N : HalfClosedTime → Ω → ℝ)
    (H η π : Ω × ℝ → ℝ) (μ r σ d : ℝ) (hd : 0≤d)
    (hS : SemimartingaleDecomposition P B.F S A MS)
    (hMSI : ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*S (realTimeClamp z.2) z.1) MS)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => V (realTimeClamp z.2) z.1*(σ*π z)) N)
    (hG : SemimartingaleIntegralFormula P B.F c hc A MS H G)
    (hE : VariationIntegralFormula P c hc Bank η E)
    (hHm : ∀ w,Measurable (fun s => H (w,s)))
    (hηm : ∀ w,Measurable (fun s => η (w,s)))
    (hSm : ∀ w,Measurable (fun s => S (realTimeClamp s) w))
    (hBm : ∀ w,Measurable (fun s => Bank (realTimeClamp s) w))
    (hAe : ∀ᵐ w ∂P,∀ s∈Icc 0 d,A (realTimeClamp s) w=S ⊥ w+∫ u in 0..s,μ*S (realTimeClamp u) w)
    (hBe : ∀ᵐ w ∂P,∀ s∈Icc 0 d,Bank (realTimeClamp s) w=Bank ⊥ w+∫ u in 0..s,r*Bank (realTimeClamp u) w)
    (hAi : ∀ᵐ w ∂P,IntervalIntegrable (fun s => μ*S (realTimeClamp s) w) volume 0 d)
    (hBi : ∀ᵐ w ∂P,IntervalIntegrable (fun s => r*Bank (realTimeClamp s) w) volume 0 d)
    (hHi : ∀ᵐ w ∂P,IntervalIntegrable (fun s => H (w,s)*(μ*S (realTimeClamp s) w)) volume 0 d)
    (hηi : ∀ᵐ w ∂P,IntervalIntegrable (fun s => η (w,s)*(r*Bank (realTimeClamp s) w)) volume 0 d)
    (hshare : ∀ z,H z*S (realTimeClamp z.2) z.1=π z*V (realTimeClamp z.2) z.1)
    (hbank : ∀ᵐ w ∂P,∀ s∈Icc 0 d,η (w,s)*Bank (realTimeClamp s) w=(1-π (w,s))*V (realTimeClamp s) w)
    (x : ℝ) (he : V (realTimeClamp d)=ᵐ[P] fun w => x+
      (∫ s in 0..d,V (realTimeClamp s) w*(r+π (w,s)*(μ-r)))+N (realTimeClamp d) w) :
    V (realTimeClamp d)=ᵐ[P] fun w => x+G (realTimeClamp d) w+E (realTimeClamp d) w := by
  have hNI' : ItoCovarianceFormula P B.F (B.W 0) (fun z => H z*(σ*S (realTimeClamp z.2) z.1)) N := by
    have hh : (fun z => H z*(σ*S (realTimeClamp z.2) z.1))=(fun z => V (realTimeClamp z.2) z.1*(σ*π z)) := by
      funext z
      calc _=σ*(H z*S (realTimeClamp z.2) z.1) := by ring
           _=_ := by rw [hshare];ring
    rw [hh];exact hNI
  have hbalance : ∀ᵐ w ∂P,∀ s∈Icc 0 d,V (realTimeClamp s) w=H (w,s)*S (realTimeClamp s) w+η (w,s)*Bank (realTimeClamp s) w := by
    filter_upwards [hbank] with w hw
    intro s hs
    rw [hshare (w,s),hw s hs];ring
  have hg := market_gain_identity P B c hc hcT hcc S A MS Bank V G E N H η μ r σ d hd
    hS hMSI hN hNI' hG hE hHm hηm hSm hBm hAe hBe hAi hBi hHi hηi hbalance
  filter_upwards [he,hg] with w he hg
  have hdrift : (∫ s in 0..d,r*V (realTimeClamp s) w+(μ-r)*H (w,s)*S (realTimeClamp s) w)=
      ∫ s in 0..d,V (realTimeClamp s) w*(r+π (w,s)*(μ-r)) := by
    apply intervalIntegral.integral_congr
    intro s _
    calc _=r*V (realTimeClamp s) w+(μ-r)*(H (w,s)*S (realTimeClamp s) w) := by ring
         _=_ := by rw [hshare (w,s)];ring
  rw [hdrift] at hg
  linarith

end Asakura.Chapter11
