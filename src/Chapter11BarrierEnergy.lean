import Chapter11BarrierGradient

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency false

theorem barrier_price_smooth (b K r σ T y0 : ℝ)
    (hb : 0<b) (hK : 0<K) (hKb : K<b) (hσ : 0<σ) :
    ContDiffOn ℝ 2 (barrierBrownianPrice b K r σ T y0) {q | q 0<T} := by
  obtain ⟨hfm,hfn,hfb,hfz⟩ := barrier_log_payoff_bounds b K hb hK hKb
  exact (image_heat_smooth_harmonic _ hfm (b-K) (2*r/σ^2-1) (Real.exp (-r*T)) σ T
    (y0+(r-σ^2/2)*T) (sub_nonneg.mpr hKb.le) hfn hfb hσ.ne').2.1

/-- A uniform expected-energy estimate for the actual stopped barrier
delta, obtained from the constructed Ito integral and bounded price. -/
theorem barrier_delta_prefix_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T R y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hR : 0<R) (hRT : R<T) (hy0 : y0<0) :
    (∀ w,IntervalIntegrable (fun t => barrierGradient P B b K r σ T y0 (w,t)^2) volume 0 R) ∧
      Integrable (fun w => ∫ t in 0..R,barrierGradient P B b K r σ T y0 (w,t)^2) P ∧
      (∫ w,(∫ t in 0..R,barrierGradient P B b K r σ T y0 (w,t)^2) ∂P)≤
        (2*(Real.exp (-r*T)*(b-K)))^2 := by
  obtain ⟨τ,N,hτe,hτ,hN,hNI,he⟩ := barrier_preterminal_constructed P B b K r σ T R y0 hb hK hKb hσ hR.le hRT hy0
  let G := fun z : Ω × ℝ => (Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ z.1).val)).indicator
    (fun _ => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
      ![(finitePrefixTime (T:=(⊤:EReal)) R hR.le (realTimeClamp z.2)).val,B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)
  obtain ⟨hp,hi⟩ := stopped_open_gradient_regularity P B R T hR.le hRT _
    (barrier_price_smooth b K r σ T y0 hb hK hKb hσ) (fun w => realTimeClamp (τ w).val) hτ
  have heval w : barrierStoppedPrice P B b K r σ T y0 R w=
      barrierBrownianPrice b K r σ T y0 ![(τ w).val,B.W 0 (realTimeClamp (τ w).val) w] := by
    dsimp only [barrierStoppedPrice]
    rw [←hτe,changed_time_real _ (τ w).property.1]
  have hbound : ∀ᵐ w ∂P,|barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp R) w|≤Real.exp (-r*T)*(b-K) := by
    filter_upwards [he,barrier_stopped_price_bounds P B b K r σ T y0 R hb hK hKb hσ hy0 ⟨hR.le,hRT⟩] with w hw hbw
    have heR := hw R ⟨hR.le,le_rfl⟩
    rw [min_eq_left (τ w).property.2] at heR
    rw [←heR,←heval,abs_of_nonneg hbw.1]
    exact hbw.2
  obtain ⟨hfm,hfn,hfb,hfz⟩ := barrier_log_payoff_bounds b K hb hK hKb
  have hν : (2*r/σ^2-1)*σ^2=2*r-σ^2 := by
    simpa only [mul_comm (2*r/σ^2-1) (σ^2)] using barrier_reflection_parameter r σ hσ.ne'
  have hzero := image_brownian_price_bounds (barrierLogPayoff b K) hfm (b-K) (2*r/σ^2-1)
    r σ T y0 0 0 (sub_nonneg.mpr hKb.le) hfn hfb hfz hσ.ne' hν (hR.trans hRT)
    (by simpa using hy0.le)
  have ha : |barrierBrownianPrice b K r σ T y0 ![0,0]|≤Real.exp (-r*T)*(b-K) := by
    change |brownianHeatPrice (imageHeat (barrierLogPayoff b K) (2*r/σ^2-1)) (Real.exp (-r*T)) σ T (y0+(r-σ^2/2)*T) ![0,0]|≤_
    rw [abs_of_nonneg hzero.1]
    exact hzero.2
  obtain ⟨hEi,hEb⟩ := stopped_price_energy_bound P B G hp (fun d hd => ae_of_all _ (hi d hd)) N hN hNI R _ _ hR.le
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hKb.le)) ha hbound
  have heg w t (ht : t∈Icc 0 R) : G (w,t)=barrierGradient P B b K r σ T y0 (w,t) :=
    barrier_gradient_prefix_eq P B b K r σ T R y0 hR.le τ hτe w t ht
  have hei w : (∫ t in 0..R,G (w,t)^2)=(∫ t in 0..R,barrierGradient P B b K r σ T y0 (w,t)^2) :=
    intervalIntegral.integral_congr (fun t ht => by rw [heg w t (by simpa [uIcc_of_le hR.le] using ht)])
  refine ⟨?_,by simpa only [hei] using hEi,by simpa only [hei] using hEb⟩
  intro w
  apply (hi R hR w).congr
  intro t ht
  have ht' : t∈Ioc 0 R := by simpa [uIoc_of_le hR.le] using ht
  change G (w,t)^2=_
  rw [heg w t ⟨ht'.1.le,ht'.2⟩]

/-- Monotone convergence gives finite total energy up to maturity for
the actual barrier hedge, including the singular terminal corner. -/
theorem barrier_delta_terminal_energy {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hT : 0<T) (hy0 : y0<0) :
    Integrable (fun z => barrierGradient P B b K r σ T y0 z^2) (P.prod (volume.restrict (Ioo 0 T))) ∧
      (∫ z,barrierGradient P B b K r σ T y0 z^2 ∂P.prod (volume.restrict (Ioo 0 T)))≤
        (2*(Real.exp (-r*T)*(b-K)))^2 := by
  obtain ⟨c,hc,hcm,hcT,hu⟩ := positive_interval_exhaustion T hT
  apply terminal_square_energy_from_prefix_bounds P _ (barrier_gradient_measurable P B b K r σ T y0) T _
    c (fun n => (hc n).le) hcm hu
  · intro n
    exact ae_of_all _ (barrier_delta_prefix_energy P B b K r σ T (c n) y0 hb hK hKb hσ (hc n) (hcT n) hy0).1
  · intro n
    exact (barrier_delta_prefix_energy P B b K r σ T (c n) y0 hb hK hKb hσ (hc n) (hcT n) hy0).2.1
  · intro n
    exact (barrier_delta_prefix_energy P B b K r σ T (c n) y0 hb hK hKb hσ (hc n) (hcT n) hy0).2.2

end Asakura.Chapter11
