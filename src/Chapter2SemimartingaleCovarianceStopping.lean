import Chapter2SemimartingaleDecomposition
import Chapter2OneSidedStoppedCovariance

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false

/-- All three stopping identities for S, with the stopped decompositions
constructed in the original spaces. Covariation is defined by the martingale parts. -/
theorem semimartingale_covariance_stopping
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y A M B N C D E G : ClosedTime T → Ω → ℝ)
    (hX : SemimartingaleDecomposition P F X A M)
    (hY : SemimartingaleDecomposition P F Y B N)
    (hC : LocalCovarianceWitness P F M N C)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hD : LocalCovarianceWitness P F (fun t ω => M (min (τ ω) t) ω) N D)
    (hE : LocalCovarianceWitness P F M (fun t ω => N (min (τ ω) t) ω) E)
    (hG : LocalCovarianceWitness P F (fun t ω => M (min (τ ω) t) ω)
      (fun t ω => N (min (τ ω) t) ω) G) :
    SemimartingaleDecomposition P F (fun t ω => X (min (τ ω) t) ω)
      (fun t ω => A (min (τ ω) t) ω) (fun t ω => M (min (τ ω) t) ω) ∧
    SemimartingaleDecomposition P F (fun t ω => Y (min (τ ω) t) ω)
      (fun t ω => B (min (τ ω) t) ω) (fun t ω => N (min (τ ω) t) ω) ∧
    (∀ᵐ ω ∂P, ∀ t, t < ⊤ → G t ω = C (min (τ ω) t) ω ∧
      D t ω = C (min (τ ω) t) ω ∧ E t ω = C (min (τ ω) t) ω) := by
  exact ⟨hX.stopped P F hF hle τ hτ,hY.stopped P F hF hle τ hτ,
    local_covariance_stopping_exercise P F hF hle hnull M N C D E G
      hX.martingale hY.martingale hC τ hτ hD hE hG⟩

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.semimartingale_covariance_stopping
