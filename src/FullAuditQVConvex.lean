import FullAuditMartingaleHilbert
import FullAuditQVGrid
import Chapter1WrittenSteps

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Asakura.FullAudit
open Asakura.Chapter1Written Asakura.Chapter2Written
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Terminal values admitting a continuous martingale representative for
 which X squared minus that representative increases on the specified grid. -/
def gridConstrainedTerminals {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (X : ClosedTime T → Ω → ℝ)
    (D : Set (ClosedTime T)) : Set (continuousM2Terminal P F) :=
  {v | ∃ Y, ContinuousM2Witness P F Y ∧ Y ⊤ =ᵐ[P] (v : Lp ℝ 2 P) ∧
    ∀ s ∈ D, ∀ t ∈ D, s ≤ t →
      (fun ω => X s ω ^ 2-Y s ω) ≤ᵐ[P] (fun ω => X t ω ^ 2-Y t ω)}

theorem grid_constrained_terminals_convex {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (X : ClosedTime T → Ω → ℝ)
    (D : Set (ClosedTime T)) : Convex ℝ (gridConstrainedTerminals P F X D) := by
  rintro u ⟨U,hU,hu,hDU⟩ v ⟨V,hV,hv,hDV⟩ a b ha hb hab
  refine ⟨fun t => a • U t+b • V t,(hU.smul P F a).add P F (hV.smul P F b),?_,?_⟩
  · have h := ((hu.const_smul a).add (hv.const_smul b)).trans
      (((Lp.coeFn_smul a (u : Lp ℝ 2 P)).add (Lp.coeFn_smul b (v : Lp ℝ 2 P))).symm)
    exact h.trans (Lp.coeFn_add (a • (u : Lp ℝ 2 P)) (b • (v : Lp ℝ 2 P))).symm
  · intro s hs t ht hst
    filter_upwards [hDU s hs t ht hst,hDV s hs t ht hst] with ω h₁ h₂
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    have h := add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
    calc
      _ = a*(X s ω^2-U s ω)+b*(X s ω^2-V s ω) := by nlinarith [congrArg (fun c => c*X s ω^2) hab]
      _ ≤ _ := h
      _ = _ := by nlinarith [congrArg (fun c => c*X t ω^2) hab]

/-- The actual finite square sums increase on every coarser dyadic grid. -/
theorem qv_partition_increases_on_coarser_grid {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (X : ClosedTime T → Ω → ℝ) {n k : ℕ} (hnk : n ≤ k)
    {s t : ClosedTime T} (hs : s ∈ range (qvPartition (T := T) n))
    (ht : t ∈ range (qvPartition (T := T) n)) (hst : s ≤ t) (ω : Ω) :
    partitionSquares X (qvPartition (T := T) k) (qvPartitionLength k) s ω ≤
      partitionSquares X (qvPartition (T := T) k) (qvPartitionLength k) t ω := by
  exact partition_squares_mono_on_range X (qvPartition (T := T) k) (qv_partition_mono (T := T) k)
    (qvPartitionLength k) (qv_partition_endpoints (T := T) k).2 ω
    (qv_partition_refinement (T := T) hnk hs) (qv_partition_refinement (T := T) hnk ht) hst

/-- Convex tails can be represented by actual processes, with all inequalities
 on the current grid at once. No coefficients or inequalities are assumed
 for the chosen convex combinations. -/
theorem convex_tail_grid_representatives {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (X : ClosedTime T → Ω → ℝ)
    (f g : ℕ → continuousM2Terminal P F)
    (hf : ∀ n k, n ≤ k → f k ∈ gridConstrainedTerminals P F X (range (qvPartition (T := T) n)))
    (hg : ∀ n, g n ∈ convexHull ℝ (f '' Ici n)) :
    ∀ n, g n ∈ gridConstrainedTerminals P F X (range (qvPartition (T := T) n)) := by
  intro n
  apply convexHull_min _ (grid_constrained_terminals_convex P F X _) (hg n)
  rintro v ⟨k,hk,rfl⟩
  exact hf n k hk

end Asakura.FullAudit
