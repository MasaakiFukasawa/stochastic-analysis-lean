import Chapter2LenglartLower

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written

/-- Both inequalities of Proposition lenglart, with the supremum written
as in the manuscript. No maximal or stopping estimates are hypotheses. -/
theorem local_lenglart
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ClosedTime T → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσtop : ∀ ω, σ ω < ⊤) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    P.real {ω | ε ≤ ⨆ t, |X (min (σ ω) t) ω|} - δ / ε ^ 2 ≤
      P.real {ω | δ ≤ C (σ ω) ω} ∧
    P.real {ω | δ ≤ C (σ ω) ω} ≤ ε ^ 2 / δ +
      P.real {ω | ε ≤ ⨆ t, |X (min (σ ω) t) ω|} := by
  have he (ω) : ‖localStoppedPath P F hF hle hX σ hσ hσtop ω‖ =
      ⨆ t, |X (min (σ ω) t) ω| := by
    rw [ContinuousMap.norm_eq_iSup_norm]
    rfl
  constructor
  · simpa only [he] using local_lenglart_lower P F hF hle hnull X C hX hC σ hσ hσtop ε δ hε hδ
  · simpa only [he] using local_lenglart_upper P F hF hle hnull X C hX hC σ hσ hσtop ε δ hε hδ

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_lenglart
