import Chapter11ClockIntegralIdentification
import Chapter6DriftCrossCovariance

open MeasureTheory Set Filter
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

/-- Girsanov's corrected integral is the actual Ito integral under the
 new measure. The proof transfers covariations, then identifies the
 integral; it does not assume that stochastic integrals are measure invariant. -/
theorem measure_changed_integral_identified
    {Ω : Type*} {m : MeasurableSpace Ω} (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnullP : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E=0 → MeasurableSet[F t] E)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (W X K L C A D N E : HalfClosedTime → Ω → ℝ)
    (hW : LocalMProcessWitness P F W) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F W W C)
    (hA : LocalCovarianceWitness P F X X A)
    (hD : LocalCovarianceWitness P F W X D)
    (hK : AdaptedLocalVariationWitness F K) (hL : AdaptedLocalVariationWitness F L)
    (hKc : ∀ w t,t<⊤ → ContinuousAt (fun s => K s w) t)
    (hLc : ∀ w t,t<⊤ → ContinuousAt (fun s => L s w) t)
    (hWQ : LocalMProcessWitness Q F (fun t w => W t w-K t w))
    (hXQ : LocalMProcessWitness Q F (fun t w => X t w-L t w))
    (hN : LocalMProcessWitness Q F N) (hE : LocalCovarianceWitness Q F N N E)
    (H : Ω × ℝ → ℝ) (hHm : ∀ w,Measurable (fun r => H (w,r)))
    (hNI : ItoCovarianceFormula Q F (fun t w => W t w-K t w) H N)
    (hH2 : ∀ R : ℝ,0≤R → ∀ᵐ w ∂P,IntervalIntegrable (fun r => H (w,r)^2) volume 0 R)
    (hAe : ∀ R : ℝ,0≤R → A (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r)^2)
    (hDe : ∀ R : ℝ,0≤R → D (realTimeClamp R)=ᵐ[P] fun w => ∫ r in 0..R,H (w,r))
    (hEe : ∀ R : ℝ,0≤R → E (realTimeClamp R)=ᵐ[Q] fun w => ∫ r in 0..R,H (w,r)^2) :
    (∀ᵐ w ∂Q,∀ t,t<⊤ → X t w-L t w=N t w) ∧
      (∀ᵐ w ∂P,∀ t,t<⊤ → X t w=N t w+L t w) := by
  have hAQ := drift_corrected_quadratic_variation P Q (by simp : (0:EReal)<⊤)
    F hF hle hnullP hnullQ hAE X L A hX hA hL hLc hXQ
  have hDQ := drift_corrected_cross_covariance P Q (by simp : (0:EReal)<⊤)
    F hF hle hnullP hnullQ hAE W X K L C A D hW hX hC hA hD hK hL hKc hLc hWQ hXQ
  have he := clock_integral_identification Q F hF hle
    (fun t w => W t w-K t w) (fun t w => X t w-L t w) N A E D
    hWQ hXQ hN hAQ hE hDQ H hHm hNI
    (fun R hR => (hAE _).mp (hH2 R hR))
    (fun R hR => (hAE _).mp (hAe R hR)) hEe (fun R hR => (hAE _).mp (hDe R hR))
  refine ⟨he,?_⟩
  filter_upwards [(hAE _).mpr he] with w hw
  intro t ht
  linarith [hw t ht]

end Asakura.Chapter11
