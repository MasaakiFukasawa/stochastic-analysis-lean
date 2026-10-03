import Chapter2LocalCovarianceRules
import Chapter2LocalNonnegative

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Zero local quadratic variation forces the process to vanish, even
when the zero identity initially holds only outside a common null set. -/
theorem local_zero_variation_implies_zero
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X C : ClosedTime T → Ω → ℝ) (hC : LocalCovarianceWitness P F X X C)
    (hz : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = 0) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = 0 := by
  have hpos : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → 0 ≤ X t ω*X t ω-C t ω := by
    filter_upwards [hz] with ω hω
    intro t ht
    rw [hω t ht,sub_zero]
    exact mul_self_nonneg _
  have h := nonnegative_local_martingale_zero P F hF hle _ hC.defect hpos
  filter_upwards [h,hz] with ω hω hcω
  intro t ht
  have he := hω t ht
  rw [hcω t ht,sub_zero,← pow_two] at he
  exact sq_eq_zero_iff.mp he

/-- Proposition 2.5.3: test the covariations against the difference process,
use the proved local bilinearity, and apply the zero-variation result. The
covariations are characterized by the constructed existence/uniqueness result. -/
theorem local_covariance_separates
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X X' : ClosedTime T → Ω → ℝ)
    (hX : LocalMProcessWitness P F X) (hX' : LocalMProcessWitness P F X')
    (hcov : ∀ Y, LocalMProcessWitness P F Y →
      ∃ C D, LocalCovarianceWitness P F X Y C ∧ LocalCovarianceWitness P F X' Y D ∧
        ∀ᵐ ω ∂P, ∀ t, t < ⊤ → C t ω = D t ω) :
    ∀ᵐ ω ∂P, ∀ t, t < ⊤ → X t ω = X' t ω := by
  let Z := fun t ω => X t ω-X' t ω
  have hZ : LocalMProcessWitness P F Z := by
    have h := hX.add P F hF hle (hX'.smul P F (-1))
    convert h using 1
    funext t ω
    dsimp only [Z]
    ring
  obtain ⟨C,D,hC,hD,he⟩ := hcov Z hZ
  have hZZ : LocalCovarianceWitness P F Z Z (fun t ω => -D t ω+C t ω) := by
    have h := hD.bilinear P F hF hle hC (-1)
    convert h using 1 <;> funext t ω <;> (try dsimp only [Z]) <;> ring
  have hzC : ∀ᵐ ω ∂P, ∀ t, t < ⊤ → -D t ω+C t ω = 0 := by
    filter_upwards [he] with ω hω
    intro t ht
    rw [hω t ht]
    ring
  have hz := local_zero_variation_implies_zero P F hF hle Z _ hZZ hzC
  exact hz.mono fun ω hω t ht => sub_eq_zero.mp (hω t ht)

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.local_zero_variation_implies_zero
#print axioms Asakura.Chapter2Complete.local_covariance_separates
