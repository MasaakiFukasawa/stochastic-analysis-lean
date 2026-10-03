import Chapter11BarrierPriceProcess

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

theorem barrier_log_stock_regular {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (y0 r σ : ℝ) :
    (∀ t,t<⊤ → Measurable[B.F t] (barrierLogStock P B y0 r σ t)) ∧
      (∀ w t,t<⊤ → ContinuousAt (fun s => barrierLogStock P B y0 r σ s w) t) ∧
      (∀ᵐ w ∂P,barrierLogStock P B y0 r σ ⊥ w=y0) := by
  refine ⟨fun t ht => (((B.martingale 0).adapted P B.F t ht).const_mul σ).const_add _,?_,?_⟩
  · intro w t ht
    exact (continuousAt_const.add (continuousAt_const.mul (changed_time_coordinate_continuousAt t ht))).add
      (continuousAt_const.mul ((B.martingale 0).path P B.F w t ht))
  · filter_upwards [(B.martingale 0).initial P B.F] with w hw
    simp only [barrierLogStock,show (halfTimeReal (⊥ : HalfClosedTime) : ℝ)=0 from rfl,hw,Pi.zero_apply,mul_zero,add_zero]

theorem barrier_payoff_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hT : 0≤T) :
    Measurable[B.F (realTimeClamp T)] (barrierDiscountedPayoff P B b K r σ T y0) := by
  obtain ⟨hXa,hXc,_⟩ := barrier_log_stock_regular P B y0 r σ
  have hs := open_continuous_hitting_stopping B.F B.mono (barrierLogStock P B y0 r σ) hXa hXc (Ici 0) isClosed_Ici
  have hsurv : MeasurableSet[B.F (realTimeClamp T)]
      {w | realTimeClamp T<upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)} := by
    convert (hs (realTimeClamp T)).compl using 1
    ext w
    simp only [mem_setOf_eq,mem_compl_iff,not_le,upperBarrierHit,mem_Ici]
  have hpay := (((hXa _ (real_time_below T hT (EReal.coe_lt_top T))).exp.const_mul b).sub_const K).max (measurable_const (a:=(0:ℝ)))
  exact (Measurable.ite hsurv hpay measurable_const).const_mul _

theorem barrier_stopped_price_bounds {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 t : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hy0 : y0<0) (ht : t∈Ico 0 T) :
    ∀ᵐ w ∂P,0≤barrierStoppedPrice P B b K r σ T y0 t w ∧
      barrierStoppedPrice P B b K r σ T y0 t w≤Real.exp (-r*T)*(b-K) := by
  obtain ⟨hXa,hXc,hX0⟩ := barrier_log_stock_regular P B y0 r σ
  obtain ⟨hfm,hfn,hfb,hfz⟩ := barrier_log_payoff_bounds b K hb hK hKb
  filter_upwards [hX0] with w hw
  let hit := upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)
  let ρ := min hit (realTimeClamp t)
  have hρtop : ρ<⊤ := (min_le_right _ _).trans_lt (real_time_below t ht.1 (EReal.coe_lt_top t))
  obtain ⟨q,hq,hqt,hqe⟩ := finite_closed_time_real ρ hρtop
  have hqle : q≤t := by
    have hh : realTimeClamp (T:=(⊤:EReal)) q≤realTimeClamp t := hqe ▸ min_le_right _ _
    change (realTimeClamp q:EReal)≤(realTimeClamp t:EReal) at hh
    rw [real_time_clamp_eq q hq le_top,real_time_clamp_eq t ht.1 le_top] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hregion := before_upper_hit_nonpos (fun s => barrierLogStock P B y0 r σ s w) (hXc w)
    (by rw [hw];exact hy0) q hq (hqe.le.trans (min_le_left _ _))
  have hregion' : y0+(r-σ^2/2)*q+σ*B.W 0 (realTimeClamp q) w≤0 := by
    simpa only [barrierLogStock,changed_time_real q hq] using hregion
  have hν : (2*r/σ^2-1)*σ^2=2*r-σ^2 := by
    simpa only [mul_comm (2*r/σ^2-1) (σ^2)] using barrier_reflection_parameter r σ hσ.ne'
  have hbound := image_brownian_price_bounds (barrierLogPayoff b K) hfm (b-K) (2*r/σ^2-1)
    r σ T y0 q (B.W 0 (realTimeClamp q) w) (sub_nonneg.mpr hKb.le) hfn hfb hfz hσ.ne' hν (hqle.trans_lt ht.2) hregion'
  change 0≤barrierBrownianPrice b K r σ T y0 ![(halfTimeReal ρ : ℝ),B.W 0 ρ w] ∧
    barrierBrownianPrice b K r σ T y0 ![(halfTimeReal ρ : ℝ),B.W 0 ρ w]≤Real.exp (-r*T)*(b-K)
  rw [←hqe,changed_time_real q hq]
  exact hbound

/-- Actual barrier valuation from the Gaussian construction, first hitting
time, Ito formula, boundedness, and terminal limit. No conditional price
formula is included among the assumptions. -/
theorem barrier_actual_conditional_price {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hT : 0<T) (hy0 : y0<0) :
    ∀ t∈Ico 0 T,P[barrierDiscountedPayoff P B b K r σ T y0|B.F (realTimeClamp t)]=ᵐ[P]
      barrierStoppedPrice P B b K r σ T y0 t := by
  apply bounded_preterminal_price_conditional P B.F B.le (barrierStoppedPrice P B b K r σ T y0)
    (barrierDiscountedPayoff P B b K r σ T y0) T (barrierBrownianPrice b K r σ T y0 ![0,0])
    (Real.exp (-r*T)*(b-K)) hT
  · intro R hR hRT
    exact (barrier_price_preterminal_representation P B b K r σ T R y0 hb hK hKb hσ hR hRT hy0).1
  · intro t ht
    exact ((barrier_price_preterminal_representation P B b K r σ T t y0 hb hK hKb hσ ht.1 ht.2 hy0).2 t ⟨ht.1,le_rfl⟩).stronglyMeasurable
  · exact ((barrier_payoff_measurable P B b K r σ T y0 hT.le).mono (B.le _) le_rfl).aestronglyMeasurable
  · intro t ht
    exact (barrier_stopped_price_bounds P B b K r σ T y0 t hb hK hKb hσ hy0 ht).mono fun w hw => by rw [abs_of_nonneg hw.1];exact hw.2
  · exact barrier_stopped_terminal_limit P B b K r σ T y0 hb hK hKb hσ hT hy0

end Asakura.Chapter11
