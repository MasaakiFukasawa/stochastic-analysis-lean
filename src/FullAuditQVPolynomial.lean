import FullAuditCovarianceBilinear

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)

theorem bounded_cov_diagonal (X : boundedMProcess P F) :
    ∀ᵐ ω ∂P, ∀ t, boundedCov P F hF hle hnull X X t ω = boundedQV P F hF hle hnull X t ω := by
  have hQ := boundedQV_properties P F hF hle hnull X
  have hM : ContinuousM2Witness P F (fun t ω => X.val t ω*X.val t ω-boundedQV P F hF hle hnull X t ω) := by
    simpa only [pow_two] using hQ.2.2.2
  have hA (ω) : ∃ B C : ClosedTime T → ℝ, Monotone B ∧ Monotone C ∧
      ∀ t, boundedQV P F hF hle hnull X t ω = B t-C t :=
    ⟨fun t => boundedQV P F hF hle hnull X t ω,fun _ => 0,hQ.2.2.1 ω,monotone_const,fun t => (sub_zero _).symm⟩
  exact (bounded_cov_unique P F hF hle hnull X X _ hA hM).mono fun ω hω t => (hω t).symm

/-- Polarization and the verified bilinearity give the full quadratic
 polynomial, with one exceptional null set for each scalar. -/
theorem bounded_qv_quadratic (X Y : boundedMProcess P F) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, boundedQV P F hF hle hnull (c • X+Y) t ω =
      c^2*boundedQV P F hF hle hnull X t ω+2*c*boundedCov P F hF hle hnull X Y t ω+
      boundedQV P F hF hle hnull Y t ω := by
  let C := boundedCov P F hF hle hnull
  let Q := boundedQV P F hF hle hnull
  let Z := c • X+Y
  filter_upwards [bounded_cov_diagonal P F hF hle hnull Z,
    bounded_cov_bilinear P F hF hle hnull X Y Z c,
    bounded_cov_symmetric P F hF hle hnull X Z,
    bounded_cov_symmetric P F hF hle hnull Y Z,
    bounded_cov_bilinear P F hF hle hnull X Y X c,
    bounded_cov_bilinear P F hF hle hnull X Y Y c,
    bounded_cov_symmetric P F hF hle hnull Y X,
    bounded_cov_diagonal P F hF hle hnull X,
    bounded_cov_diagonal P F hF hle hnull Y] with ω hD hB hSX hSY hBX hBY hS hDX hDY
  intro t
  change Q Z t ω = c^2*Q X t ω+2*c*C X Y t ω+Q Y t ω
  dsimp only [Q,C]
  dsimp only [Z] at hD hB hSX hSY hBX hBY ⊢
  rw [← hD t,hB t,hSX t,hSY t,hBX t,hBY t,hS t,hDX t,hDY t]
  ring

end Asakura.FullAudit
