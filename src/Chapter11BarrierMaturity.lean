import Chapter11BarrierEnergy

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency false

/-- The actual barrier delta integral is constructed through maturity;
its terminal gain equals the discounted payoff less the initial price. -/
theorem barrier_delta_integral_at_maturity {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hT : 0<T) (hy0 : y0<0) :
    ∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => (Iic T).indicator (fun t => barrierGradient P B b K r σ T y0 (z.1,t)) z.2) N ∧
      (∀ t∈Ico 0 T,(fun w => barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp t) w)=ᵐ[P]
        barrierStoppedPrice P B b K r σ T y0 t) ∧
      ((fun w => barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp T) w)=ᵐ[P]
        barrierDiscountedPayoff P B b K r σ T y0) := by
  let H := barrierGradient P B b K r σ T y0
  have hH := barrier_gradient_measurable P B b K r σ T y0
  obtain ⟨N,hN,hNl,hNI⟩ := finite_energy_integral_constructed P B H hH T hT.le
    (barrier_gradient_progressive P B b K r σ T y0 T hT.le)
    (barrier_delta_terminal_energy P B b K r σ T y0 hb hK hKb hσ hT hy0).1
  let G := fun z : Ω × ℝ => (Iic T).indicator (fun t => H (z.1,t)) z.2
  have hG : Measurable G := by
    change Measurable ((Prod.snd ⁻¹' Iic T).indicator H)
    exact hH.indicator (measurableSet_Iic.preimage measurable_snd)
  have heR R (hR : 0≤R) (hRT : R<T) :
      (fun w => barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp R) w)=ᵐ[P]
        barrierStoppedPrice P B b K r σ T y0 R := by
    obtain ⟨τ,L,hτe,hτ,hL,hLI,heL⟩ := barrier_preterminal_constructed P B b K r σ T R y0 hb hK hKb hσ hR hRT hy0
    let J := fun z : Ω × ℝ => (Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ z.1).val)).indicator
      (fun _ => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
        ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)
    have hJ w : Measurable (fun t => J (w,t)) := by
      obtain ⟨hm,_,_⟩ := open_price_gradient_regularity P B R T hR hRT _ (barrier_price_smooth b K r σ T y0 hb hK hKb hσ)
      have hs : MeasurableSet {t : ℝ | realTimeClamp (T:=(⊤:EReal)) t∈Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ w).val)} :=
        real_time_clamp_continuous.measurable measurableSet_Ioc
      exact (hm.comp measurable_prodMk_left).indicator hs
    obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (T:=(⊤:EReal)) (by simp)
    have hLl := continuous_m2_is_local P B.F B.mono B.le
      (fun n => realTimeClamp (c n)) hct.monotone hcut hcc L hL
    have heG w t (ht : t∈Ioc 0 R) : G (w,t)=J (w,t) := by
      dsimp only [G]
      rw [Set.indicator_of_mem (show t∈Iic T from ht.2.trans hRT.le)]
      exact (barrier_gradient_prefix_eq P B b K r σ T R y0 hR τ hτe w t ⟨ht.1.le,ht.2⟩).symm
    have he := progressive_ito_prefix_congr P B G J (fun w => hG.comp measurable_prodMk_left) hJ
      N L hNl hLl hNI hLI R hR heG
    filter_upwards [he,heL] with w hw hwL
    have hn := hw (realTimeClamp R) (real_time_below R hR (EReal.coe_lt_top R))
    rw [min_self] at hn
    rw [hn,←hwL R ⟨hR,le_rfl⟩,min_eq_left (τ w).property.2]
    dsimp only [barrierStoppedPrice]
    rw [←hτe,changed_time_real _ (τ w).property.1]
  refine ⟨N,hN,hNI,fun t ht => heR t ht.1 ht.2,?_⟩
  obtain ⟨c,hcm,hc,hlim⟩ := exists_seq_strictMono_tendsto' hT
  have hleft : Tendsto c atTop (𝓝[<] T) := tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall fun n => (hc n).2⟩
  filter_upwards [ae_all_iff.mpr (fun n => heR (c n) (hc n).1.le (hc n).2),
    barrier_stopped_terminal_limit P B b K r σ T y0 hb hK hKb hσ hT hy0] with w hw hlimw
  have hn : Tendsto (fun n => barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp (c n)) w)
      atTop (𝓝 (barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp T) w)) :=
    (continuous_const.add ((hN.path w).comp real_time_clamp_continuous)).continuousAt.tendsto.comp hlim
  have hv := hlimw.comp hleft
  simp only [Function.comp_def] at hv
  simp_rw [hw] at hn
  exact tendsto_nhds_unique hn hv

end Asakura.Chapter11
