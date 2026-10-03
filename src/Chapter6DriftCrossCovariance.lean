import Chapter6DriftCovarianceTransfer

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Polarization transfers actual cross covariances as well as quadratic
variations, so the Brownian measure-change argument works in all dimensions. -/
theorem drift_corrected_cross_covariance
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnullP : ∀ t E,MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E = 0 → MeasurableSet[F t] E)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (Y Z K L C D E : ClosedTime T → Ω → ℝ)
    (hY : LocalMProcessWitness P F Y) (hZ : LocalMProcessWitness P F Z)
    (hC : LocalCovarianceWitness P F Y Y C) (hD : LocalCovarianceWitness P F Z Z D)
    (hE : LocalCovarianceWitness P F Y Z E)
    (hK : AdaptedLocalVariationWitness F K) (hL : AdaptedLocalVariationWitness F L)
    (hKc : ∀ w t,t < ⊤ → ContinuousAt (fun s => K s w) t)
    (hLc : ∀ w t,t < ⊤ → ContinuousAt (fun s => L s w) t)
    (hV : LocalMProcessWitness Q F (fun t w => Y t w-K t w))
    (hU : LocalMProcessWitness Q F (fun t w => Z t w-L t w)) :
    LocalCovarianceWitness Q F (fun t w => Y t w-K t w) (fun t w => Z t w-L t w) E := by
  have hYS := hY.add P F hF hle hZ
  have hS : LocalCovarianceWitness P F (fun t w => Y t w+Z t w) (fun t w => Y t w+Z t w)
      (fun t w => C t w+2*E t w+D t w) := by
    refine ⟨?_,(hC.variation.add F (hE.variation.smul F 2)).add F hD.variation⟩
    have hd := (hC.defect.add P F hF hle (hE.defect.smul P F 2)).add P F hF hle hD.defect
    convert hd using 1
    funext t w
    ring
  have hSU : LocalMProcessWitness Q F (fun t w => (Y t w+Z t w)-(K t w+L t w)) := by
    convert hV.add Q F hF hle hU using 1
    funext t w
    ring
  have hSC := drift_corrected_quadratic_variation P Q hT F hF hle hnullP hnullQ hAE
    _ _ _ hYS hS (hK.add hL hF) (fun w t ht => (hKc w t ht).add (hLc w t ht)) hSU
  have hVC := drift_corrected_quadratic_variation P Q hT F hF hle hnullP hnullQ hAE Y K C hY hC hK hKc hV
  have hUD := drift_corrected_quadratic_variation P Q hT F hF hle hnullP hnullQ hAE Z L D hZ hD hL hLc hU
  refine ⟨?_,hE.variation⟩
  have hd := ((hSC.defect.add Q F hF hle (hVC.defect.smul Q F (-1))).add Q F hF hle
    (hUD.defect.smul Q F (-1))).smul Q F (1/2)
  convert hd using 1
  funext t w
  ring

end Asakura.Chapter6
