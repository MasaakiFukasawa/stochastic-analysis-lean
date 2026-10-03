import Chapter2LocalCovarianceCS
import Chapter2CovarianceProbabilityBound
import Chapter2LenglartConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- Adaptedness of covariance below the terminal time follows from the
product-minus-covariance characterization, with no terminal value used. -/
theorem LocalCovarianceWitness.adapted
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    {X Y C : ClosedTime T → Ω → ℝ}
    (hC : LocalCovarianceWitness P F X Y C)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (t : ClosedTime T) (ht : t < ⊤) : Measurable[F t] (C t) := by
  have h := ((hX.adapted P F t ht).mul (hY.adapted P F t ht)).sub
    (hC.defect.adapted P F t ht)
  convert h using 1
  funext ω
  change C t ω = X t ω*Y t ω-(X t ω*Y t ω-C t ω)
  ring

/-- Actual covariations with a fixed local martingale tend to zero in
probability when the first local martingale tends locally uniformly to zero.
The quadratic variation of the fixed process need not have a finite mean. -/
theorem local_covariance_probability_of_local_martingale
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X A C : ℕ → ClosedTime T → Ω → ℝ) (Y B : ClosedTime T → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P F (X n)) (hY : LocalMProcessWitness P F Y)
    (hA : ∀ n, LocalCovarianceWitness P F (X n) (X n) (A n))
    (hB : LocalCovarianceWitness P F Y Y B)
    (hC : ∀ n, LocalCovarianceWitness P F (X n) Y (C n))
    (t : ClosedTime T) (ht : t < ⊤)
    (hprob : ∀ ε > 0, Tendsto (fun n => P {ω | ε ≤ ⨆ s, |X n (min t s) ω|}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ |C n t ω|}) atTop (𝓝 0) := by
  have hstop : ∀ s, MeasurableSet[F s] {ω : Ω | t ≤ s} := by
    intro s
    by_cases hs : t ≤ s <;> simp [hs]
  have hsmall := quadratic_variation_probability_of_local_martingale P F hF hle hnull
    X A hX hA (fun _ => t) hstop (fun _ => ht) hprob
  apply covariance_probability_from_square_bound P (fun n => C n t) (fun n => A n t)
    (B t) ((hB.adapted P F hY hY t ht).mono (hle t) le_rfl) _ hsmall ε hε
  intro n
  filter_upwards [local_covariance_point_cs P F hF hle hnull
    (X n) Y (A n) B (C n) (hX n) hY (hA n) hB (hC n)] with ω hω
  exact hω t ht

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.LocalCovarianceWitness.adapted
#print axioms Asakura.Chapter2Complete.local_covariance_probability_of_local_martingale
