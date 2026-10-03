import Chapter6BracketInvariance
import Chapter6ItoCovarianceVariation

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter11
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter6
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- The common clock in the progressive measure-invariance theorem is
 derived from the two actual price decompositions. -/
theorem market_quadratic_variation_transfer {Ω : Type*} {m : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {T : EReal} [Fact (0≤T)] (hT : 0<T)
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t≤m)
    (hnullP : ∀ t E,MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (hnullQ : ∀ t E,MeasurableSet[m] E → Q E=0 → MeasurableSet[F t] E)
    (hAE : ∀ p : Ω → Prop,(∀ᵐ w ∂P,p w) ↔ ∀ᵐ w ∂Q,p w)
    (S A M B N C : ClosedTime T → Ω → ℝ)
    (hP : SemimartingaleDecomposition P F S A M)
    (hQ : SemimartingaleDecomposition Q F S B N)
    (hC : LocalCovarianceWitness P F M M C) : LocalCovarianceWitness Q F N N C := by
  obtain ⟨D,hD⟩ := local_covariance_witness_exists Q F hF hle hnullQ N N hQ.martingale hQ.martingale
  have he := semimartingale_quadratic_variation_invariant P Q hT F hF hle hnullP hnullQ hAE
    S A M B N C D hP hQ hC hD
  refine ⟨?_,hC.variation⟩
  apply LocalMProcessWitness.congr_ae_open Q F hF hD.defect
  · intro t ht
    exact ((hQ.martingale.adapted Q F t ht).mul (hQ.martingale.adapted Q F t ht)).sub
      (hC.adapted P F hP.martingale hP.martingale t ht)
  · intro w t ht
    exact ((hQ.martingale.path Q F w t ht).mul (hQ.martingale.path Q F w t ht)).sub
      (local_covariance_path_continuous P F M M C hP.martingale hP.martingale hC w t ht)
  · filter_upwards [(hAE _).mp he] with w hw
    intro t ht
    rw [hw t ht]

end Asakura.Chapter11
