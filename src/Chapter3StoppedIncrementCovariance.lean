import Chapter3WeightedLocalMartingale
import Chapter3ContinuousAdaptedWeights
import Chapter2OneSidedStoppedCovariance
import Chapter2LocalCovarianceAE

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter3Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- The actual stopped covariance, not an unspecified equal representative,
is a covariance witness. This makes its zero-before-stop property usable. -/
theorem actual_one_sided_stopped_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (σ : Ω → ClosedTime T) (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) :
    LocalCovarianceWitness P F (fun t ω => X (min (σ ω) t) ω) Y
      (fun t ω => C (min (σ ω) t) ω) := by
  have hXs := hX.stopped P F hF hle σ hσ
  obtain ⟨D,hD⟩ := local_covariance_witness_exists P F hF hle hnull _ Y hXs hY
  have he := local_covariance_one_sided_stopping P F hF hle hnull X Y C D hX hY hC σ hσ hD
  have hXr := hX.stopped_regular P F hF hle σ hσ hσt
  have hCr := hC.stopped_regular P F hF hle hX hY σ hσ hσt
  let Z := fun t ω => X (min (σ ω) t) ω*Y t ω-C (min (σ ω) t) ω
  have hZm (t) (ht : t < ⊤) : Measurable[F t] (Z t) := by
    convert ((hXr.1 t).mul (hY.adapted P F t ht)).sub (hCr.1 t) using 1
  have hZc (ω t) (ht : t < ⊤) : ContinuousAt (fun s => Z s ω) t := by
    convert (((hXr.2 ω).continuousAt).mul (hY.path P F ω t ht)).sub ((hCr.2 ω).continuousAt) using 1
  refine ⟨hD.defect.congr_ae_of_stopped_regular P F ?_ ?_,hC.variation.stopped F σ⟩
  · filter_upwards [he] with ω hω
    intro t ht
    rw [hω t ht]
  · intro ρ hρ hρt
    exact open_continuous_adapted_stopped_regular F hF Z hZm hZc c hcm hct hcc ρ hρ hρt

/-- Covariance of a stopping interval increment with an arbitrary local
martingale, in its literal difference form. -/
theorem actual_stopped_increment_covariance
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)
    (X Y C : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hY : LocalMProcessWitness P F Y)
    (hC : LocalCovarianceWitness P F X Y C)
    (c : ℕ → ClosedTime T) (hcm : Monotone c) (hct : ∀ n, c n < ⊤)
    (hcc : ∀ t, t < ⊤ → ∃ n, t < c n)
    (σ τ : Ω → ClosedTime T)
    (hσ : ∀ t, MeasurableSet[F t] {ω | σ ω ≤ t})
    (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t})
    (hσt : ∀ ω, σ ω < ⊤) (hτt : ∀ ω, τ ω < ⊤) :
    LocalCovarianceWitness P F
      (fun t ω => X (min (τ ω) t) ω-X (min (σ ω) t) ω) Y
      (fun t ω => C (min (τ ω) t) ω-C (min (σ ω) t) ω) := by
  have hs := actual_one_sided_stopped_covariance P F hF hle hnull X Y C hX hY hC c hcm hct hcc σ hσ hσt
  have ht := actual_one_sided_stopped_covariance P F hF hle hnull X Y C hX hY hC c hcm hct hcc τ hτ hτt
  convert hs.bilinear P F hF hle ht (-1) using 1 <;> (funext t ω; ring)

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.actual_one_sided_stopped_covariance
#print axioms Asakura.Chapter3Complete.actual_stopped_increment_covariance
