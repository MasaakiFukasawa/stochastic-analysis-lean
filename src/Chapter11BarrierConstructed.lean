import Chapter11BarrierStoppedPrice
import Chapter11BarrierHitting
import Chapter11BarrierReflection

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

noncomputable def barrierLogStock {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (y0 r σ : ℝ) (t : HalfClosedTime) (w : Ω) : ℝ :=
  y0+(r-σ^2/2)*(halfTimeReal t : ℝ)+σ*B.W 0 t w

noncomputable def barrierLogPayoff (b K z : ℝ) : ℝ :=
  if z<0 then max (b*Real.exp z-K) 0 else 0

noncomputable def barrierBrownianPrice (b K r σ T y0 : ℝ) : (Fin 2 → ℝ) → ℝ :=
  brownianHeatPrice (imageHeat (barrierLogPayoff b K) (2*r/σ^2-1))
    (Real.exp (-r*T)) σ T (y0+(r-σ^2/2)*T)

/-- The complete preterminal stopped integral, starting from the actual
Brownian stock and the actual barrier payoff. The stopping-time property,
pre-hit bound, Gaussian PDE, Ito construction and M2 upgrade are derived. -/
theorem barrier_preterminal_constructed {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T R y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hR : 0≤R) (hRT : R<T) (hy0 : y0<0) :
    ∃ τ : Ω → Icc (0:ℝ) R,∃ N : HalfClosedTime → Ω → ℝ,
      (∀ w,realTimeClamp (τ w).val=
        min (upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)) (realTimeClamp R)) ∧
      (∀ t,MeasurableSet[B.F t] {w | realTimeClamp (τ w).val≤t}) ∧
      ContinuousM2Witness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0)
        (fun z => (Ioc (⊥ : HalfClosedTime) (realTimeClamp (τ z.1).val)).indicator
          (fun _ => fderiv ℝ (barrierBrownianPrice b K r σ T y0)
            ![(finitePrefixTime (T:=(⊤:EReal)) R hR (realTimeClamp z.2)).val,
              B.W 0 (realTimeClamp z.2) z.1] (Pi.single 1 1)) (realTimeClamp z.2)) N ∧
      (∀ᵐ w ∂P,∀ t∈Icc 0 R,
        barrierBrownianPrice b K r σ T y0
          ![min (τ w).val t,B.W 0 (realTimeClamp (min (τ w).val t)) w]=
        barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp t) w) := by
  let X := barrierLogStock P B y0 r σ
  have hXa t (ht : t<⊤) : Measurable[B.F t] (X t) :=
    (((B.martingale 0).adapted P B.F t ht).const_mul σ).const_add _
  have hXc w t (ht : t<⊤) : ContinuousAt (fun s => X s w) t :=
    (continuousAt_const.add (continuousAt_const.mul (changed_time_coordinate_continuousAt t ht))).add
      (continuousAt_const.mul ((B.martingale 0).path P B.F w t ht))
  have hX0 : ∀ᵐ w ∂P,X ⊥ w<0 := by
    filter_upwards [(B.martingale 0).initial P B.F] with w hw
    simpa only [X,barrierLogStock,show (halfTimeReal (⊥ : HalfClosedTime) : ℝ)=0 from rfl,hw,Pi.zero_apply,mul_zero,add_zero] using hy0
  obtain ⟨τ,hτe,hτ,hreg⟩ := upper_hit_finite_cap P B.F B.mono X hXa hXc hX0 R hR
  obtain ⟨hfm,hfn,hfb,hfz⟩ := barrier_log_payoff_bounds b K hb hK hKb
  have hν : (2*r/σ^2-1)*σ^2=2*r-σ^2 := by
    simpa only [mul_comm (2*r/σ^2-1) (σ^2)] using barrier_reflection_parameter r σ hσ.ne'
  have hregion : ∀ᵐ w ∂P,∀ t∈Icc 0 R,
      y0+(r-σ^2/2)*min (τ w).val t+σ*B.W 0 (realTimeClamp (min (τ w).val t)) w≤0 := by
    filter_upwards [hreg] with w hw
    intro t ht
    have hh := hw t ht
    simpa only [X,barrierLogStock,changed_time_real _ (le_min (τ w).property.1 ht.1)] using hh
  obtain ⟨N,hN,hNI,he⟩ := image_price_stopped_integral P B (barrierLogPayoff b K) hfm (b-K) _ r σ T R y0
    (sub_nonneg.mpr hKb.le) hfn hfb hfz hσ.ne' hν hR hRT τ hτ hregion
  refine ⟨τ,N,hτe,hτ,hN,hNI,?_⟩
  filter_upwards [he,(B.martingale 0).initial P B.F] with w hw hz
  intro t ht
  simpa only [barrierBrownianPrice,hz,Pi.zero_apply] using hw t ht

end Asakura.Chapter11
