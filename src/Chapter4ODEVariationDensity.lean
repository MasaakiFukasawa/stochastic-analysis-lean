import Chapter4ODEPathVariation
import Chapter5TimeDensityVariation
import Chapter3VariationIntegratorCongruence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter5
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- An ordinary differential equation identifies the constructed Stieltjes
integral against its solution with the time integral of the derivative. -/
theorem ode_variation_integral_density
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {T : EReal} [Fact (0≤T)]
    (Y J : ClosedTime T → Ω → ℝ) (G H : Ω × ℝ → ℝ)
    (hYc : ∀ w t,t<⊤ → ContinuousAt (fun s => Y s w) t)
    (hGm : ∀ w,Measurable (fun r => G (w,r)))
    (hGc : ∀ w (R : ℝ),0≤R → (R:EReal)<T → ContinuousOn (fun r => G (w,r)) (Icc 0 R))
    (hd : ∀ w (r : ℝ),0<r → (r:EReal)<T →
      HasDerivAt (fun s => Y (realTimeClamp s) w) (G (w,r)) r)
    (c : ℕ → ℝ) (hc : ∀ n,0≤c n) (hcT : ∀ n,(c n:EReal)<T)
    (hcc : ∀ t,t<⊤ → ∃ n,t<realTimeClamp (T := T) (c n))
    (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hHc : ∀ n w,ContinuousOn (fun r => H (w,r)) (Icc 0 (c n)))
    (hJ : VariationIntegralFormula P c hc Y H J)
    (d : ℝ) (hd0 : 0≤d) (hdT : (d:EReal)<T) :
    J (realTimeClamp d)=ᵐ[P] fun w => ∫ r in 0..d,H (w,r)*G (w,r) := by
  have hz : realTimeClamp (T := T) 0=⊥ := by
    apply Subtype.ext
    change (realTimeClamp (T := T) 0:EReal)=0
    simpa only [EReal.coe_zero] using real_time_clamp_eq (T := T) 0 le_rfl (show (0:EReal)≤T from Fact.out)
  let B := fun t w => Y t w-Y ⊥ w
  have hb : ∀ n,∀ᵐ w ∂P,∀ r∈Icc 0 (c n),B (realTimeClamp r) w=∫ s in 0..r,G (w,s) := by
    intro n
    apply ae_of_all
    intro w r hr
    have hrT : (r:EReal)<T := (EReal.coe_le_coe hr.2).trans_lt (hcT n)
    have hy : ContinuousOn (fun s : ℝ => Y (realTimeClamp s) w) (Icc 0 r) := by
      intro s hs
      exact ((hYc w _ (real_time_below s hs.1 ((EReal.coe_le_coe hs.2).trans_lt hrT))).comp
        real_time_clamp_continuous.continuousAt).continuousWithinAt
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hy
      (fun s hs => hd w s hs.1 ((EReal.coe_lt_coe hs.2).trans hrT))
      ((hGc w r hr.1 hrT).intervalIntegrable_of_Icc hr.1)
    simpa only [B,hz] using he.symm
  have hj := variation_integral_integrator_increments_congr P Y B J H c hc hcT hJ
    (ae_of_all _ fun _ _ _ _ _ => by dsimp [B]; ring)
  exact time_density_variation_integral P B J G H c hc hcT hcc hb hGm
    (fun n => ae_of_all _ fun w => (hGc w _ (hc n) (hcT n)).intervalIntegrable_of_Icc (hc n))
    hHm hHc hj d hd0 hdT

end Asakura.Chapter4
