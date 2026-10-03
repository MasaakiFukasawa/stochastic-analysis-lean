import Chapter11MeasurableTimeDensity

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- The two bank terms in the discount product rule combine into the
stock-discount correction. Holdings are merely measurable. Every term is
an actual Stieltjes integral, identified through its time density. -/
theorem bank_discount_drift_cancellation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)]
    (B D I J K : ClosedTime T → Ω → ℝ)
    (r H η S V : Ω × ℝ → ℝ)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T:=T) (c n))
    (d : ℝ) (hd : 0≤d) (hdT : (d:EReal)<T)
    (hB : ∀ᵐ w ∂P,∀ t∈Icc 0 d,B (realTimeClamp t) w=B ⊥ w+∫ u in 0..t,r (w,u)*B (realTimeClamp u) w)
    (hD : ∀ᵐ w ∂P,∀ t∈Icc 0 d,D (realTimeClamp t) w=D ⊥ w+∫ u in 0..t,-r (w,u)*D (realTimeClamp u) w)
    (hBm : ∀ w,Measurable (fun t => r (w,t)*B (realTimeClamp t) w))
    (hDm : ∀ w,Measurable (fun t => -r (w,t)*D (realTimeClamp t) w))
    (hBi : ∀ᵐ w ∂P,IntervalIntegrable (fun t => r (w,t)*B (realTimeClamp t) w) volume 0 d)
    (hDi : ∀ᵐ w ∂P,IntervalIntegrable (fun t => -r (w,t)*D (realTimeClamp t) w) volume 0 d)
    (hηm : ∀ w,Measurable (fun t => D (realTimeClamp t) w*η (w,t)))
    (hVm : ∀ w,Measurable (fun t => V (w,t)))
    (hHSm : ∀ w,Measurable (fun t => H (w,t)*S (w,t)))
    (hηi : ∀ᵐ w ∂P,IntervalIntegrable (fun t => (D (realTimeClamp t) w*η (w,t))*(r (w,t)*B (realTimeClamp t) w)) volume 0 d)
    (hVi : ∀ᵐ w ∂P,IntervalIntegrable (fun t => V (w,t)*(-r (w,t)*D (realTimeClamp t) w)) volume 0 d)
    (hHSi : ∀ᵐ w ∂P,IntervalIntegrable (fun t => (H (w,t)*S (w,t))*(-r (w,t)*D (realTimeClamp t) w)) volume 0 d)
    (hbalance : ∀ᵐ w ∂P,∀ t∈Icc 0 d,V (w,t)=H (w,t)*S (w,t)+η (w,t)*B (realTimeClamp t) w)
    (hI : VariationIntegralFormula P c hc B (fun z => D (realTimeClamp z.2) z.1*η z) I)
    (hJ : VariationIntegralFormula P c hc D V J)
    (hK : VariationIntegralFormula P c hc D (fun z => H z*S z) K) :
    (fun w => I (realTimeClamp d) w+J (realTimeClamp d) w)=ᵐ[P] K (realTimeClamp d) := by
  have hi := measurable_time_density_variation_integral P B I (B ⊥) (fun z => r z*B (realTimeClamp z.2) z.1) (fun z => D (realTimeClamp z.2) z.1*η z) c hc hcT hcc d hd hdT hB hBm hBi hηm hηi hI
  have hj := measurable_time_density_variation_integral P D J (D ⊥) (fun z => -r z*D (realTimeClamp z.2) z.1) V c hc hcT hcc d hd hdT hD hDm hDi hVm hVi hJ
  have hk := measurable_time_density_variation_integral P D K (D ⊥) (fun z => -r z*D (realTimeClamp z.2) z.1) (fun z => H z*S z) c hc hcT hcc d hd hdT hD hDm hDi hHSm hHSi hK
  filter_upwards [hi,hj,hk,hηi,hVi,hbalance] with w hwI hwJ hwK hηw hVw hb
  rw [hwI,hwJ,hwK,←intervalIntegral.integral_add hηw hVw]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc 0 d := by simpa only [uIcc_of_le hd] using ht
  dsimp only
  rw [hb t ht']
  ring

end Asakura.Chapter11
