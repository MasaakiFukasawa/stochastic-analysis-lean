import Chapter11MeasurableTimeDensity
import Chapter11GeneralAssociativity
import Chapter4FinitePathLift
import Chapter4BrownianSystem

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- For the stock and bank account, the actual gains integrals are exactly
 the Brownian wealth equation used in replication and optimal investment.
 Holdings are measurable, not necessarily continuous. -/
theorem market_gain_identity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<⊤)
    (hcc : ∀ t : HalfClosedTime,t<⊤ → ∃ n,t<realTimeClamp (c n))
    (S A MS Bank V G E N : HalfClosedTime → Ω → ℝ)
    (H η : Ω × ℝ → ℝ) (μ r σ d : ℝ) (hd : 0≤d)
    (hS : SemimartingaleDecomposition P B.F S A MS)
    (hMSI : ItoCovarianceFormula P B.F (B.W 0) (fun z => σ*S (realTimeClamp z.2) z.1) MS)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => H z*(σ*S (realTimeClamp z.2) z.1)) N)
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
    (hbalance : ∀ᵐ w ∂P,∀ s∈Icc 0 d,V (realTimeClamp s) w=H (w,s)*S (realTimeClamp s) w+η (w,s)*Bank (realTimeClamp s) w) :
    (fun w => G (realTimeClamp d) w+E (realTimeClamp d) w)=ᵐ[P]
      fun w => (∫ s in 0..d,r*V (realTimeClamp s) w+(μ-r)*H (w,s)*S (realTimeClamp s) w)+N (realTimeClamp d) w := by
  obtain ⟨J,L,hGL,hJ,hL⟩ := hG
  have hJe := measurable_time_density_variation_integral P A J (S ⊥)
    (fun z => μ*S (realTimeClamp z.2) z.1) H c hc hcT hcc d hd (EReal.coe_lt_top d)
    hAe (fun w => (hSm w).const_mul μ) hAi hHm hHi hJ
  have hEe := measurable_time_density_variation_integral P Bank E (Bank ⊥)
    (fun z => r*Bank (realTimeClamp z.2) z.1) η c hc hcT hcc d hd (EReal.coe_lt_top d)
    hBe (fun w => (hBm w).const_mul r) hBi hηm hηi hE
  have hLN := ito_integral_associativity P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W 0) MS L N (fun z => σ*S (realTimeClamp z.2) z.1) H
    (B.martingale 0) hS.martingale hGL.martingale hN (fun w => (hSm w).const_mul σ) hHm hMSI hL hNI
  filter_upwards [hJe,hEe,hLN,hHi,hηi,hbalance] with w hj he hn hi hη hw
  rw [hGL.decomposition _ (real_time_below d hd (EReal.coe_lt_top d)) w,hj,he,hn _ (real_time_below d hd (EReal.coe_lt_top d))]
  have hiSum := intervalIntegral.integral_add hi hη
  have hiEq : (∫ s in 0..d,H (w,s)*(μ*S (realTimeClamp s) w)+η (w,s)*(r*Bank (realTimeClamp s) w))=
      ∫ s in 0..d,r*V (realTimeClamp s) w+(μ-r)*H (w,s)*S (realTimeClamp s) w := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hd] at hs
    dsimp only
    rw [hw s hs]
    ring
  linarith

end Asakura.Chapter11
