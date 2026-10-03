import Chapter6BracketInvariance
import Chapter6ItoCovarianceVariation

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter6
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- After a measure change, subtraction of the constructed finite-variation
drift preserves the original bracket. Both decompositions are constructed
here; their membership is not assumed for an arbitrary semimartingale. -/
theorem drift_corrected_quadratic_variation
    {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0 ≤ T)] (hT : 0 < T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ m)
    (hnullP : ∀ t E,MeasurableSet[m] E → P E = 0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E = 0 → MeasurableSet[F t] E)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (Y K C : ClosedTime T → Ω → ℝ)
    (hY : LocalMProcessWitness P F Y) (hC : LocalCovarianceWitness P F Y Y C)
    (hK : AdaptedLocalVariationWitness F K)
    (hKc : ∀ w t,t < ⊤ → ContinuousAt (fun s => K s w) t)
    (hV : LocalMProcessWitness Q F (fun t w => Y t w-K t w)) :
    LocalCovarianceWitness Q F (fun t w => Y t w-K t w) (fun t w => Y t w-K t w) C := by
  let V := fun t w => Y t w-K t w
  have hc w t ht : ContinuousAt (fun s => V s w) t := (hY.path P F w t ht).sub (hKc w t ht)
  have hP : SemimartingaleDecomposition P F V (fun t w => -1*K t w) Y :=
    ⟨hK.smul (-1),hY,hc,fun t ht w => by dsimp [V]; ring⟩
  have hQ : SemimartingaleDecomposition Q F V (fun t w => 0*K t w) V :=
    ⟨hK.smul 0,hV,hc,fun t ht w => by ring⟩
  obtain ⟨D,hD⟩ := local_covariance_witness_exists Q F hF hle hnullQ V V hV hV
  have he := semimartingale_quadratic_variation_invariant P Q hT F hF hle hnullP hnullQ hAE
    V (fun t w => -1*K t w) Y (fun t w => 0*K t w) V C D hP hQ hC hD
  refine ⟨?_,hC.variation⟩
  apply Asakura.Chapter3Complete.LocalMProcessWitness.congr_ae_open Q F hF hD.defect
  · intro t ht
    exact ((hV.adapted Q F t ht).mul (hV.adapted Q F t ht)).sub (hC.adapted P F hY hY t ht)
  · intro w t ht
    exact ((hc w t ht).mul (hc w t ht)).sub (local_covariance_path_continuous P F Y Y C hY hY hC w t ht)
  · filter_upwards [(hAE _).mp he] with w hw
    intro t ht
    rw [hw t ht]

end Asakura.Chapter6
