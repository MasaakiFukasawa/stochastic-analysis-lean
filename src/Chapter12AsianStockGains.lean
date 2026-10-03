import Chapter12AsianBrownianClark
import Chapter12ScalarStockGains
import Chapter12FiniteConditionalPrice
import Chapter12CanonicalClock

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem asian_brownian_stock_gains {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hpaths : ∀ w,Continuous (fun t => B t w))
    (T : ℝ≥0) (hT : 0<T) [Fact (0≤(T:ℝ))]
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    let c := canonicalClock
    let hco := canonical_clock_properties.2.2.2.2.2
    let BS := naturalBrownianSystem P B hB hm hpaths
    let Sd := fun z : Ω × ℝ => geometricFlow x 0 σ
      ![BS.C 0 0 (realTimeClamp z.2) z.1,BS.W 0 (realTimeClamp z.2) z.1]
    let X := brownianCompactPath B hpaths T
    let E := progressiveEnergyIntegrands BS.F c (P.prod (volume.restrict (Ioi (0:ℝ))))
    let M2 := fun N => ContinuousM2Witness P BS.F N
    let Ito := fun (H : E) N => ItoCovarianceFormula P BS.F (BS.W 0) H.val N
    let restrict := fun H : E =>
      ((terminal_integrand_restriction P BS.F BS.mono BS.le c hco H T T.property).2).toLp
        (fun z : Ω × Icc (0:ℝ) T => H.val (z.1,z.2.val))
    let R := P.trim (BS.le (realTimeClamp T))
    let Pay := fun w => Real.exp (-r*T)*max (asianPathAverage x r T T.property σ (X w)-K) 0
    let Price := fun N => ∀ t,t≤realTimeClamp T → P[Pay|BS.F t] =ᵐ[P]
      (fun w => (∫ z,Pay z ∂R)+N t w)
    let Gains := fun (H : E) N => ∃ Y : HalfClosedTime → Ω → ℝ,LocalMProcessWitness P BS.F Y ∧
        ItoCovarianceFormula P BS.F (BS.W 0) (fun z => σ*Sd z) Y ∧
        ItoCovarianceFormula P BS.F Y (fun z => H.val z/(σ*Sd z)) N ∧
        ∀ᵐ w ∂P,∀ t : ℝ,0≤t →
          geometricFlow x 0 σ ![t,BS.W 0 (realTimeClamp t) w]=x+Y (realTimeClamp t) w
    letI := probability_trim P _ (BS.le (realTimeClamp T))
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    ∃ H : E,∃ N : HalfClosedTime → Ω → ℝ,
      M2 N ∧ Ito H N ∧
      Pay =ᵐ[P] (fun w => (∫ z,Pay z ∂R)+N (realTimeClamp T) w) ∧
      Price N ∧
      Gains H N ∧
      ∀ᵐ t ∂compactTimeMeasure T T.property,∀ᵐ w ∂R,
        restrict H (w,t)/(σ*Real.exp (-r*t.val)*stockPathValue x σ r T (X w) t)=
          Real.exp (-r*(T-t.val))/(T*stockPathValue x σ r T (X w) t)*
            R[(fun v => (if K<asianPathAverage x r T T.property σ (X v) then (1:ℝ) else 0)*
              asianRemainingMoment T T.property x σ r 0 (X v) t)|BS.F (realTimeClamp t.val)] w := by
  let BS := naturalBrownianSystem P B hB hm hpaths
  have hmain := asian_brownian_clark_holdings P B hB hm hpaths T hT x σ r K hx hσ
  have hp := finite_represented_conditional_price P BS.F BS.le
  dsimp only at hmain ⊢
  obtain ⟨H,N,hN,hNI,hrep,hhold⟩ := hmain
  have hg := scalar_stock_gains P BS 0 x σ hx.ne' hσ.ne' H.val H.property.1 N hN hNI
  exact ⟨H,N,hN,hNI,hrep,(hp N hN _ _ _ hrep).2,hg,hhold⟩

end Asakura.Chapter12

#print axioms Asakura.Chapter12.asian_brownian_stock_gains
