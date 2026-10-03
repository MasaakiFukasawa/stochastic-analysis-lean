import Chapter11BarrierValuation
import Chapter11BarrierStockHit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

/-- The stopped Brownian-coordinate price is the discounted, surviving
call/digital combination printed in the manuscript. -/
theorem barrier_stopped_printed_price {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 t : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hy0 : y0<0) (ht : t∈Ico 0 T) :
    barrierStoppedPrice P B b K r σ T y0 t=ᵐ[P]
      fun w => Real.exp (-r*t)*(if realTimeClamp t<upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)
        then barrierStockPrice b K r σ (T-t) (b*Real.exp (y0+(r-σ^2/2)*t+σ*B.W 0 (realTimeClamp t) w)) else 0) := by
  obtain ⟨hXa,hXc,hX0⟩ := barrier_log_stock_regular P B y0 r σ
  filter_upwards [hX0] with w hw
  let X := fun s => barrierLogStock P B y0 r σ s w
  let τ := upperBarrierHit X
  by_cases hsurv : realTimeClamp t<τ
  · change barrierBrownianPrice b K r σ T y0 ![(halfTimeReal (min τ (realTimeClamp t)) : ℝ),B.W 0 (min τ (realTimeClamp t)) w]=_
    rw [min_eq_right hsurv.le,changed_time_real t ht.1,if_pos hsurv]
    exact barrier_brownian_stock_identity b K r σ T y0 t _ hb hK hKb hσ ht.2
  · have hτt : τ≤realTimeClamp t := le_of_not_gt hsurv
    have hτtop : τ<⊤ := hτt.trans_lt (real_time_below t ht.1 (EReal.coe_lt_top t))
    obtain ⟨q,hq,hqt,hqe⟩ := finite_closed_time_real τ hτtop
    have hqle : q≤t := by
      have hh := hτt
      rw [←hqe] at hh
      change (realTimeClamp q:EReal)≤(realTimeClamp t:EReal) at hh
      rw [real_time_clamp_eq q hq le_top,real_time_clamp_eq t ht.1 le_top] at hh
      exact EReal.coe_le_coe_iff.mp hh
    have hhit := at_upper_hit_zero X (hXc w) (by change barrierLogStock P B y0 r σ ⊥ w<0;rw [hw];exact hy0) hτtop
    have hboundary : barrierBrownianPrice b K r σ T y0 ![q,B.W 0 τ w]=0 := by
      apply barrier_brownian_boundary b K r σ T y0 q _ hσ (hqle.trans_lt ht.2)
      change y0+(r-σ^2/2)*(halfTimeReal τ : ℝ)+σ*B.W 0 τ w=0 at hhit
      rw [←hqe,changed_time_real q hq] at hhit
      simpa only [hqe] using hhit
    change barrierBrownianPrice b K r σ T y0 ![(halfTimeReal (min τ (realTimeClamp t)) : ℝ),B.W 0 (min τ (realTimeClamp t)) w]=_
    rw [min_eq_left hτt,if_neg hsurv,mul_zero,←hqe,changed_time_real q hq,hqe]
    exact hboundary

/-- Conditional valuation with the actual initial stock s and the exact
call/digital formula. The logarithmic first hit equals the stock first hit
by barrier_hit_stock_equivalence. -/
theorem barrier_printed_conditional_price {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T s t : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hT : 0<T) (hs : 0<s) (hsb : s<b) (ht : t∈Ico 0 T) :
    let τ := fun w => upperBarrierHit (fun u => barrierLogStock P B (Real.log (s/b)) r σ u w)
    P[(fun w => Real.exp (-r*T)*(if realTimeClamp T<τ w
      then max (s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)-K) 0 else 0))|B.F (realTimeClamp t)]=ᵐ[P]
      fun w => Real.exp (-r*t)*(if realTimeClamp t<τ w
        then barrierStockPrice b K r σ (T-t) (s*Real.exp ((r-σ^2/2)*t+σ*B.W 0 (realTimeClamp t) w)) else 0) := by
  dsimp only
  obtain ⟨hy,_,hstock⟩ := barrier_stock_log_coordinates b s hb hs hsb
  have hCE := barrier_actual_conditional_price P B b K r σ T (Real.log (s/b)) hb hK hKb hσ hT hy t ht
  have hprice := barrier_stopped_printed_price P B b K r σ T (Real.log (s/b)) t hb hK hKb hσ hy ht
  have hpay : barrierDiscountedPayoff P B b K r σ T (Real.log (s/b))=
      fun w => Real.exp (-r*T)*(if realTimeClamp T<upperBarrierHit (fun u => barrierLogStock P B (Real.log (s/b)) r σ u w)
        then max (s*Real.exp ((r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)-K) 0 else 0) := by
    funext w
    dsimp only [barrierDiscountedPayoff,barrierLogStock]
    rw [changed_time_real T hT.le,add_assoc,hstock]
  rw [hpay] at hCE
  filter_upwards [hCE,hprice] with w hw hp
  rw [hw,hp,add_assoc,hstock]

end Asakura.Chapter11
