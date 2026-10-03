import Chapter11BarrierMovingEndpoint
import Chapter11BarrierTerminal
import Chapter11EuropeanTerminal

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

noncomputable def barrierStoppedPrice {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (b K r σ T y0 t : ℝ) (w : Ω) : ℝ :=
  let ρ := min (upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)) (realTimeClamp t)
  barrierBrownianPrice b K r σ T y0 ![(halfTimeReal ρ : ℝ),B.W 0 ρ w]

noncomputable def barrierDiscountedPayoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (b K r σ T y0 : ℝ) (w : Ω) : ℝ :=
  Real.exp (-r*T)*(if realTimeClamp T<upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)
    then max (b*Real.exp (barrierLogStock P B y0 r σ (realTimeClamp T) w)-K) 0 else 0)

theorem brownian_log_terminal_no_atom {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (y0 r σ T : ℝ) (hσ : 0<σ) (hT : 0<T) :
    ∀ᵐ w ∂P,barrierLogStock P B y0 r σ (realTimeClamp T) w≠0 := by
  have hl := brownian_standardized_law P (T:=(⊤:EReal)) (by simp) B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    (fun w t ht _ => B.diagonal_clock 0 w t ht) T hT (EReal.coe_lt_top T)
  have he : {w | barrierLogStock P B y0 r σ (realTimeClamp T) w=0}=
      {w | B.W 0 (realTimeClamp T) w/Real.sqrt T=-(y0+(r-σ^2/2)*T)/(σ*Real.sqrt T)} := by
    ext w
    change barrierLogStock P B y0 r σ (realTimeClamp T) w=0 ↔ B.W 0 (realTimeClamp T) w/Real.sqrt T=-(y0+(r-σ^2/2)*T)/(σ*Real.sqrt T)
    dsimp only [barrierLogStock]
    rw [changed_time_real T hT.le]
    constructor <;> intro h
    · field_simp [hσ.ne',Real.sqrt_ne_zero'.mpr hT]
      linarith
    · field_simp [hσ.ne',Real.sqrt_ne_zero'.mpr hT] at h
      linarith
  have hn : P {w | barrierLogStock P B y0 r σ (realTimeClamp T) w=0}=0 := by
    rw [he,hl.measure_eq (p:=fun z => z=-(y0+(r-σ^2/2)*T)/(σ*Real.sqrt T)) (measurableSet_singleton _)]
    letI := nullSingletonClass_gaussianReal (μ:=0) (v:=1) (by norm_num)
    exact measure_singleton _
  simpa only [ae_iff,not_not] using hn

/-- The corner is excluded using the actual Gaussian law. Early knockout
and survival are treated separately, yielding the printed terminal payoff. -/
theorem barrier_stopped_terminal_limit {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hT : 0<T) (hy0 : y0<0) :
    ∀ᵐ w ∂P,Tendsto (fun t => barrierStoppedPrice P B b K r σ T y0 t w) (𝓝[<] T)
      (𝓝 (barrierDiscountedPayoff P B b K r σ T y0 w)) := by
  filter_upwards [brownian_log_terminal_no_atom P B y0 r σ T hσ hT,(B.martingale 0).initial P B.F] with w hne hW0
  let X := fun s => barrierLogStock P B y0 r σ s w
  let τ := upperBarrierHit X
  have hXc t (ht : t<⊤) : ContinuousAt X t :=
    (continuousAt_const.add (continuousAt_const.mul (changed_time_coordinate_continuousAt t ht))).add
      (continuousAt_const.mul ((B.martingale 0).path P B.F w t ht))
  have hX0 : X ⊥<0 := by
    simpa only [X,barrierLogStock,show (halfTimeReal (⊥ : HalfClosedTime) : ℝ)=0 from rfl,hW0,Pi.zero_apply,mul_zero,add_zero] using hy0
  by_cases hτ : τ<realTimeClamp T
  · have hτtop : τ<⊤ := hτ.trans (real_time_below T hT.le (EReal.coe_lt_top T))
    obtain ⟨q,hq,hqt,hqe⟩ := finite_closed_time_real τ hτtop
    have hqT : q<T := by
      rw [←hqe] at hτ
      change (realTimeClamp q:EReal)<(realTimeClamp T:EReal) at hτ
      rw [real_time_clamp_eq q hq le_top,real_time_clamp_eq T hT.le le_top] at hτ
      exact EReal.coe_lt_coe_iff.mp hτ
    have hhit := at_upper_hit_zero X hXc hX0 hτtop
    have hboundary : barrierBrownianPrice b K r σ T y0 ![q,B.W 0 τ w]=0 := by
      apply barrier_brownian_boundary b K r σ T y0 q _ hσ hqT
      have hh := hhit
      change y0+(r-σ^2/2)*(halfTimeReal τ : ℝ)+σ*B.W 0 τ w=0 at hh
      rw [←hqe,changed_time_real q hq] at hh
      simpa only [hqe] using hh
    have hU : barrierDiscountedPayoff P B b K r σ T y0 w=0 := by
      change Real.exp (-r*T)*(if realTimeClamp T<τ then _ else 0)=0
      rw [if_neg (not_lt_of_ge hτ.le),mul_zero]
    rw [hU]
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_gt_nhds hqT).filter_mono nhdsWithin_le_nhds] with t ht
    have hτt : τ≤realTimeClamp t := by rw [←hqe];exact real_time_clamp_mono ht.le
    dsimp only [barrierStoppedPrice]
    change (0:ℝ)=barrierBrownianPrice b K r σ T y0 ![(halfTimeReal (min τ (realTimeClamp t)) : ℝ),B.W 0 (min τ (realTimeClamp t)) w]
    rw [min_eq_left hτt,←hqe,changed_time_real q hq,hqe,hboundary]
  · have hTτ : realTimeClamp T≤τ := le_of_not_gt hτ
    have hx := before_upper_hit_nonpos X hXc hX0 T hT.le hTτ
    have hxneg : X (realTimeClamp T)<0 := lt_of_le_of_ne hx hne
    have hsurvive : realTimeClamp T<τ := lt_of_le_of_ne hTτ (by
      intro he
      have hτtop : τ<⊤ := by rw [←he];exact real_time_below T hT.le (EReal.coe_lt_top T)
      have hh := at_upper_hit_zero X hXc hX0 hτtop
      change X τ=0 at hh
      rw [←he] at hh
      exact hne hh)
    have hneg : y0+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w<0 := by
      simpa only [X,barrierLogStock,changed_time_real T hT.le] using hxneg
    have hcW : ContinuousAt (fun t : ℝ => B.W 0 (realTimeClamp t) w) T :=
      ((B.martingale 0).path P B.F w _ (real_time_below T hT.le (EReal.coe_lt_top T))).comp real_time_clamp_continuous.continuousAt
    have hl := barrier_brownian_moving_endpoint b K r σ T y0 hb hK hKb hσ _ hcW hneg
    have hU : barrierDiscountedPayoff P B b K r σ T y0 w=
        Real.exp (-r*T)*max (b*Real.exp (y0+(r-σ^2/2)*T+σ*B.W 0 (realTimeClamp T) w)-K) 0 := by
      change Real.exp (-r*T)*(if realTimeClamp T<τ then max (b*Real.exp (X (realTimeClamp T))-K) 0 else 0)=_
      rw [if_pos hsurvive]
      simp only [X,barrierLogStock,changed_time_real T hT.le]
    rw [hU]
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin,(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht ht0
    have hle : realTimeClamp t≤τ := (real_time_clamp_mono ht.le).trans hTτ
    simp only [barrierStoppedPrice,show min (upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)) (realTimeClamp t)=realTimeClamp t from min_eq_right hle,changed_time_real t ht0.le]

end Asakura.Chapter11
