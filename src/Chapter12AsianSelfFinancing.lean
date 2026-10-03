import Chapter12ScalarSelfFinancing
import Chapter12AsianConditionalPrice

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

noncomputable def ScalarReplication {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : BrownianSystem P d)
    (i : Fin d) (x σ r v : ℝ)
    (φ : progressiveEnergyIntegrands W.F canonicalClock (P.prod (volume.restrict (Ioi (0:ℝ)))))
    (N : HalfClosedTime → Ω → ℝ) : Prop :=
    let S := fun z : Ω × ℝ => geometricFlow x r σ ![z.2,W.W i (realTimeClamp z.2) z.1]
    let H := fun z => φ.val z/(σ*(Real.exp (-r*z.2)*S z))
    let η := fun z : Ω × ℝ => v+N (realTimeClamp z.2) z.1-φ.val z/σ
    let B := fun t w => Real.exp (r*W.C i i t w)
    ∃ Y A M G E : HalfClosedTime → Ω → ℝ,
      LocalMProcessWitness P W.F Y ∧ AdaptedLocalVariationWitness W.F A ∧
      LocalMProcessWitness P W.F M ∧ AdaptedLocalVariationWitness W.F E ∧
      (∀ᵐ w ∂P,∀ t : ℝ,0≤t → S (w,t)=(x+Y (realTimeClamp t) w)*B (realTimeClamp t) w) ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (x+Y t w)*B t w=(x+Y ⊥ w)*B ⊥ w+A t w+M t w) ∧
      SemimartingaleIntegralFormula P W.F canonicalClock (fun n => (canonical_clock_properties.1 n).le) A M H G ∧
      VariationIntegralFormula P canonicalClock (fun n => (canonical_clock_properties.1 n).le) B η E ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → (v+N t w)*B t w=(v+N ⊥ w)*B ⊥ w+G t w+E t w) ∧
      (∀ w t,H (w,t)*S (w,t)+η (w,t)*Real.exp (r*t)=Real.exp (r*t)*(v+N (realTimeClamp t) w))

theorem asian_brownian_self_financing {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (hm : ∀ t,Measurable (B t))
    (hpaths : ∀ w,Continuous (fun t => B t w))
    (T : ℝ≥0) (hT : 0<T) [Fact (0≤(T:ℝ))]
    (x σ r K : ℝ) (hx : 0<x) (hσ : 0<σ) :
    let c := canonicalClock
    let hco := canonical_clock_properties.2.2.2.2.2
    let BS := naturalBrownianSystem P B hB hm hpaths
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
    let SF := fun (φ : E) N => ScalarReplication P BS 0 x σ r (∫ z,Pay z ∂R) φ N
    letI := probability_trim P _ (BS.le (realTimeClamp T))
    letI : MeasurableSpace Ω := BS.F (realTimeClamp T)
    ∃ H : E,∃ N : HalfClosedTime → Ω → ℝ,
      M2 N ∧ Ito H N ∧
      Pay =ᵐ[P] (fun w => (∫ z,Pay z ∂R)+N (realTimeClamp T) w) ∧
      Price N ∧
      SF H N ∧
      ∀ᵐ t ∂compactTimeMeasure T T.property,∀ᵐ w ∂R,
        restrict H (w,t)/(σ*Real.exp (-r*t.val)*stockPathValue x σ r T (X w) t)=
          Real.exp (-r*(T-t.val))/(T*stockPathValue x σ r T (X w) t)*
            R[(fun v => (if K<asianPathAverage x r T T.property σ (X v) then (1:ℝ) else 0)*
              asianRemainingMoment T T.property x σ r 0 (X v) t)|BS.F (realTimeClamp t.val)] w := by
  let BS := naturalBrownianSystem P B hB hm hpaths
  have hmain := asian_brownian_clark_price P B hB hm hpaths T hT x σ r K hx hσ
  have hs := scalar_hedge_self_financing P BS 0 x σ r
  dsimp only at hmain ⊢
  obtain ⟨φ,N,hN,hNI,hrep,hprice,hhold⟩ := hmain
  exact ⟨φ,N,hN,hNI,hrep,hprice,hs _ hx hσ.ne' φ N hN hNI,hhold⟩

end Asakura.Chapter12
#print axioms Asakura.Chapter12.asian_brownian_self_financing
