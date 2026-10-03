import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
open Filter Set MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Asakura.Chapter1

/-- The finite stochastic-matrix estimate in the discrete variation proof. -/
theorem variation_partition_contraction {I J : Type*} [Fintype I] [Fintype J]
    (c : J → I → ℝ) (v : I → ℝ)
    (hpos : ∀ j i, 0 ≤ c j i) (hsum : ∀ i, ∑ j, c j i = 1) :
    ∑ j, |∑ i, c j i * v i| ≤ ∑ i, |v i| := by
  calc
    _ ≤ ∑ j, ∑ i, |c j i * v i| :=
      Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ j, c j i * |v i| := by
      simp_rw [abs_mul, abs_of_nonneg (hpos _ _)]
      exact Finset.sum_comm
    _ = ∑ i, |v i| := by simp_rw [← Finset.sum_mul, hsum, one_mul]

/-- The bound D_n ≤ |ν|(S), with the actual Mathlib total variation. -/
theorem variation_partition_upper {S : Type*} [MeasurableSpace S]
    (ν : SignedMeasure S) (π : Finset (Set S))
    (hd : (π : Set (Set S)).PairwiseDisjoint id) :
    ∑ A ∈ π, ‖ν A‖ₑ ≤ ν.totalVariation univ := by
  rw [ν.totalVariation_eq_variation]
  exact ν.le_variation MeasurableSet.univ (fun _ _ => Set.subset_univ _) hd

/-- Final squeeze step; the approximation hypotheses must be established separately.
    This does not assert the full signed-measure theorem. -/
theorem variation_limit_from_approximants (D : ℕ → ℝ) (M : ℝ)
    (hmono : Monotone D) (hupper : ∀ n, D n ≤ M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ n, M - ε < D n) :
    Tendsto D atTop (𝓝 M) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨n, hn⟩ := happrox (M-a) (sub_pos.mpr ha)
    refine eventually_atTop.mpr ⟨n, fun k hk => ?_⟩
    have := hmono hk
    linarith
  · intro b hb
    exact Filter.Eventually.of_forall fun n => lt_of_le_of_lt (hupper n) hb
end Asakura.Chapter1
