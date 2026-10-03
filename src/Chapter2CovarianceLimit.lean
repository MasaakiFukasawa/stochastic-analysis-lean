import Chapter2CovarianceContinuity
import Chapter2LocalCovarianceCongruence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Actual covariations are continuous in the first local martingale.
The difference covariance and its quadratic variation are constructed. -/
theorem covariance_probability_continuity
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X C : ℕ → ClosedTime T → Ω → ℝ) (Z Y B Q : ClosedTime T → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P F (X n))
    (hZ : LocalMProcessWitness P F Z) (hY : LocalMProcessWitness P F Y)
    (hC : ∀ n, LocalCovarianceWitness P F (X n) Y (C n))
    (hB : LocalCovarianceWitness P F Y Y B) (hQ : LocalCovarianceWitness P F Z Y Q)
    (t : ClosedTime T) (ht : t < ⊤)
    (hprob : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ⨆ s, |X n (min t s) ω-Z (min t s) ω|}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |C n t ω-Q t ω|}) atTop (𝓝 0) := by
  let D := fun n s ω => X n s ω-Z s ω
  have hD n : LocalMProcessWitness P F (D n) := by
    have h := (hX n).add P F hF hle (hZ.smul P F (-1))
    convert h using 1
    funext s ω
    dsimp [D]
    ring
  choose A hA using fun n => local_covariance_witness_exists P F hF hle hnull (D n) (D n) (hD n) (hD n)
  have hDiff n : LocalCovarianceWitness P F (D n) Y (fun s ω => C n s ω-Q s ω) := by
    have h := hQ.bilinear P F hF hle (hC n) (-1)
    change LocalCovarianceWitness P F (fun s ω => X n s ω-Z s ω) Y (fun s ω => C n s ω-Q s ω)
    convert h using 1 <;> (funext s ω; ring)
  exact local_covariance_probability_of_local_martingale P F hF hle hnull D A
    (fun n s ω => C n s ω-Q s ω) Y B hD hY hA hB hDiff t ht hprob ε hε

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.covariance_probability_continuity
