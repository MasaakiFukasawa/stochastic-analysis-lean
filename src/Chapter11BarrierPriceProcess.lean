import Chapter11BarrierStoppedLimit
import Chapter11BarrierConditional

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false

theorem barrier_price_measurable (b K r σ T y0 : ℝ) :
    Measurable (barrierBrownianPrice b K r σ T y0) := by
  have hf : Measurable (barrierLogPayoff b K) := by
    apply Measurable.ite measurableSet_Iio <;> fun_prop
  have hL : Measurable (fun q : (ℝ × ℝ) × ℝ => barrierLogPayoff b K q.2*heatLogKernel q.2 q.1) := by
    unfold heatLogKernel
    fun_prop
  have hR : Measurable (fun q : (ℝ × ℝ) × ℝ => (Real.exp (-(2*r/σ^2-1)*q.2)*barrierLogPayoff b K (-q.2))*heatLogKernel q.2 q.1) := by
    unfold heatLogKernel
    fun_prop
  have hm : Measurable (imageHeat (barrierLogPayoff b K) (2*r/σ^2-1)) :=
    (hL.stronglyMeasurable.integral_prod_right' (ν:=volume)).measurable.sub
      (hR.stronglyMeasurable.integral_prod_right' (ν:=volume)).measurable
  exact (hm.comp (show Measurable (fun q : Fin 2 → ℝ => (σ^2*(T-q 0),y0+(r-σ^2/2)*T+σ*q 1)) by fun_prop)).const_mul _

/-- The one stopped price process agrees on every preterminal interval
with the actual constructed M2 integral; the choices of capped times do
not change the process. -/
theorem barrier_price_preterminal_representation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b K r σ T R y0 : ℝ) (hb : 0<b) (hK : 0<K) (hKb : K<b)
    (hσ : 0<σ) (hR : 0≤R) (hRT : R<T) (hy0 : y0<0) :
    (∃ N : HalfClosedTime → Ω → ℝ,ContinuousM2Witness P B.F N ∧
      ∀ t∈Icc 0 R,barrierStoppedPrice P B b K r σ T y0 t=ᵐ[P]
        fun w => barrierBrownianPrice b K r σ T y0 ![0,0]+N (realTimeClamp t) w) ∧
      ∀ t∈Icc 0 R,Measurable[B.F (realTimeClamp t)] (barrierStoppedPrice P B b K r σ T y0 t) := by
  obtain ⟨τ,N,hτe,hτ,hN,hNI,he⟩ := barrier_preterminal_constructed P B b K r σ T R y0 hb hK hKb hσ hR hRT hy0
  let hit := fun w => upperBarrierHit (fun s => barrierLogStock P B y0 r σ s w)
  have heval w t (ht : t∈Icc 0 R) : barrierStoppedPrice P B b K r σ T y0 t w=
      barrierBrownianPrice b K r σ T y0 ![min (τ w).val t,B.W 0 (realTimeClamp (min (τ w).val t)) w] := by
    have hmin : min (hit w) (realTimeClamp t)=realTimeClamp (min (τ w).val t) := by
      rw [real_time_clamp_mono.map_min,hτe,min_assoc,min_eq_right (real_time_clamp_mono ht.2)]
    dsimp only [barrierStoppedPrice]
    change barrierBrownianPrice b K r σ T y0 ![(halfTimeReal (min (hit w) (realTimeClamp t)) : ℝ),B.W 0 (min (hit w) (realTimeClamp t)) w]=_
    rw [hmin,changed_time_real _ (le_min (τ w).property.1 ht.1)]
  constructor
  · refine ⟨N,hN,?_⟩
    intro t ht
    filter_upwards [he] with w hw
    rw [heval w t ht]
    exact hw t ht
  · intro t ht
    have hτtop w : realTimeClamp (T:=(⊤:EReal)) (τ w).val<⊤ := real_time_below _ (τ w).property.1 (EReal.coe_lt_top _)
    have hWm := ((B.martingale 0).stopped_regular P B.F B.mono B.le (fun w => realTimeClamp (τ w).val) hτ hτtop).1 (realTimeClamp t)
    have htm := stopped_min_measurable B.F B.mono (fun w => realTimeClamp (τ w).val) hτ (realTimeClamp t)
    have htr : Measurable[B.F (realTimeClamp t)] (fun w => (halfTimeReal (min (realTimeClamp (τ w).val) (realTimeClamp t)) : ℝ)) :=
      measurable_ereal_toReal.comp (measurable_subtype_coe.comp htm)
    letI : MeasurableSpace Ω := B.F (realTimeClamp t)
    have hm := (barrier_price_measurable b K r σ T y0).comp (show Measurable[B.F (realTimeClamp t)]
      (fun w => ![(halfTimeReal (min (realTimeClamp (τ w).val) (realTimeClamp t)) : ℝ),B.W 0 (min (realTimeClamp (τ w).val) (realTimeClamp t)) w]) by
        apply Measurable.of_eval
        intro i
        fin_cases i
        · exact htr
        · exact hWm)
    convert hm using 1
    funext w
    dsimp only [Function.comp_def]
    rw [heval w t ht,←real_time_clamp_mono.map_min,changed_time_real _ (le_min (τ w).property.1 ht.1)]

end Asakura.Chapter11
