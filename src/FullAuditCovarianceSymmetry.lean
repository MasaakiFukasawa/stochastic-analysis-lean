import FullAuditBoundedProcess

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {T : EReal} [Fact (0 ≤ T)] (F : ClosedTime T → MeasurableSpace Ω)
    (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t N, MeasurableSet[m] N → P N = 0 → MeasurableSet[F t] N)

theorem bounded_qv_homogeneous (X : boundedMProcess P F) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, boundedQV P F hF hle hnull (c • X) t ω = c^2*boundedQV P F hF hle hnull X t ω := by
  let Q := boundedQV P F hF hle hnull
  have hX := boundedQV_properties P F hF hle hnull X
  have hcX := boundedQV_properties P F hF hle hnull (c • X)
  have h := hX.2.2.2.smul P F (c^2)
  have he : (fun t => c^2 • (fun ω => X.val t ω^2-Q X t ω)) =
      (fun t ω => (c • X).val t ω^2-c^2*Q X t ω) := by
    funext t ω
    simp only [Submodule.coe_smul,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he] at h
  apply qv_uniqueness_written P F hF hle (c • X).val (Q (c • X)) (fun t ω => c^2*Q X t ω)
    hcX.2.2.1 _ hcX.2.2.2 h
  intro ω s t hst
  exact mul_le_mul_of_nonneg_left (hX.2.2.1 ω hst) (sq_nonneg c)

theorem bounded_cov_symmetric (X Y : boundedMProcess P F) :
    ∀ᵐ ω ∂P, ∀ t, boundedCov P F hF hle hnull X Y t ω = boundedCov P F hF hle hnull Y X t ω := by
  have h := bounded_qv_homogeneous P F hF hle hnull (X-Y) (-1)
  have he : (-1:ℝ) • (X-Y) = Y-X := by module
  rw [he] at h
  filter_upwards [h] with ω hω
  intro t
  simp only [boundedCov,add_comm Y X,hω t]
  norm_num

end Asakura.FullAudit
