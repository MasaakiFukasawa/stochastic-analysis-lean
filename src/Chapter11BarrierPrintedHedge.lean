import Chapter11BarrierDeltaIdentification
import Chapter11StoppingEndpoint
import Chapter11BarrierIsometry

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 3100000
set_option backward.isDefEq.respectTransparency false

noncomputable def barrierStockHedge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (z : Ω × ℝ) : ℝ :=
  if realTimeClamp (T:=(⊤:EReal)) z.2<upperBarrierHit (fun s => barrierLogStock P B y0 r σ s z.1) then
    deriv (barrierStockPrice b K r σ (T-z.2)) (b*Real.exp (barrierLogStock P B y0 r σ (realTimeClamp z.2) z.1)) else 0

/-- The actual Brownian integrand equals the exact stock hedge specified
with t < tau in the manuscript, almost everywhere in time on every path. -/
theorem barrier_printed_hedge_time_ae {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (w : Ω) :
    (fun t => Real.exp (-r*t)*σ*(b*Real.exp (barrierLogStock P B y0 r σ (realTimeClamp t) w))*
      barrierStockHedge P B b K r σ T y0 (w,t))=ᵐ[volume.restrict (Ioo 0 T)]
      fun t => barrierGradient P B b K r σ T y0 (w,t) := by
  let τ := upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)
  let g := fun t => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
    ![t,B.W 0 (realTimeClamp t) w] (Pi.single 1 1)
  have he := stopping_endpoint_time_ae τ T g
  filter_upwards [he,ae_restrict_mem measurableSet_Ioo] with t ht htT
  change (if realTimeClamp (T:=(⊤:EReal)) t<τ then g t else 0)=barrierGradient P B b K r σ T y0 (w,t) at ht
  rw [←ht]
  dsimp only [barrierStockHedge]
  change _*(if realTimeClamp (T:=(⊤:EReal)) t<τ then _ else 0)=_
  by_cases hs : realTimeClamp (T:=(⊤:EReal)) t<τ
  · rw [if_pos hs,if_pos hs]
    dsimp only [g,barrierLogStock]
    rw [changed_time_real t htT.1.le]
    exact (barrier_brownian_delta_identity b K r σ T y0 t (B.W 0 (realTimeClamp t) w) hb hK hKb hσ htT.2).symm
  · simp only [if_neg hs,mul_zero]

/-- In the original stock notation the time integral of hedge energy is
the same finite integral already constructed in Brownian coordinates. -/
theorem barrier_printed_hedge_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) (hT : 0<T) (hy0 : y0<0) :
    (∀ᵐ w ∂P,Integrable (fun t => (Real.exp (-r*t)*σ*(b*Real.exp (barrierLogStock P B y0 r σ (realTimeClamp t) w))*
      barrierStockHedge P B b K r σ T y0 (w,t))^2) (volume.restrict (Ioo 0 T))) ∧
      (∫ w,(∫ t in Ioo 0 T,(Real.exp (-r*t)*σ*(b*Real.exp (barrierLogStock P B y0 r σ (realTimeClamp t) w))*
        barrierStockHedge P B b K r σ T y0 (w,t))^2) ∂P)=
      ∫ w,(barrierDiscountedPayoff P B b K r σ T y0 w-barrierBrownianPrice b K r σ T y0 ![0,0])^2 ∂P := by
  have hi := (barrier_delta_terminal_energy P B b K r σ T y0 hb hK hKb hσ hT hy0).1
  have he w := (barrier_printed_hedge_time_ae P B b K r σ T y0 hb hK hKb hσ w).fun_comp (fun x : ℝ => x^2)
  refine ⟨?_,?_⟩
  · filter_upwards [hi.prod_right_ae] with w hw
    exact hw.congr (he w).symm
  · have hei := integral_congr_ae (ae_of_all P fun w => integral_congr_ae (he w))
    simp only [Function.comp_def] at hei
    rw [hei,←integral_prod _ hi]
    exact barrier_terminal_energy_identity P B b K r σ T y0 hb hK hKb hσ hT hy0

end Asakura.Chapter11
