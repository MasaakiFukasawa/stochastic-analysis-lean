import Chapter2CompactPathCauchy
import Chapter2RandomMetricLimit
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter2Complete
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable def pathDistance {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) : ℝ :=
  ∑' n, (1/2:ℝ)^(n+1) * min 1 (compactStageDist K n f g)

theorem path_weights_summable : Summable (fun n : ℕ => (1/2:ℝ)^(n+1)) :=
  (summable_nat_add_iff 1).2 (summable_geometric_of_abs_lt_one (by norm_num))

theorem path_weights_sum : (∑' n : ℕ, (1/2:ℝ)^(n+1)) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)]
  norm_num

theorem compact_stage_distance_nonneg {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (n : ℕ) (f g : C(D,ℝ)) : 0 ≤ compactStageDist K n f g := by
  letI : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  exact dist_nonneg

theorem path_distance_summable {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) :
    Summable (fun n => (1/2:ℝ)^(n+1) * min 1 (compactStageDist K n f g)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity)
    (le_min zero_le_one (compact_stage_distance_nonneg K n f g))) _ path_weights_summable
  intro n
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)

theorem path_distance_bounds {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) : 0 ≤ pathDistance K f g ∧ pathDistance K f g ≤ 1 := by
  refine ⟨tsum_nonneg fun n => mul_nonneg (by positivity)
    (le_min zero_le_one (compact_stage_distance_nonneg K n f g)),?_⟩
  rw [← path_weights_sum]
  apply (path_distance_summable K f g).tsum_le_tsum _ path_weights_summable
  intro n
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)

theorem path_distance_controls_stage {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g : C(D,ℝ)) (n : ℕ) :
    (1/2:ℝ)^(n+1) * min 1 (compactStageDist K n f g) ≤ pathDistance K f g :=
  (path_distance_summable K f g).le_tsum n fun j _ => mul_nonneg (by positivity)
    (le_min zero_le_one (compact_stage_distance_nonneg K j f g))

theorem path_distance_triangle {D : Type*} [TopologicalSpace D]
    (K : CompactExhaustion D) (f g h : C(D,ℝ)) :
    pathDistance K f h ≤ pathDistance K f g + pathDistance K g h := by
  letI (n : ℕ) : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  rw [pathDistance,pathDistance,pathDistance,← Summable.tsum_add
    (path_distance_summable K f g) (path_distance_summable K g h)]
  apply (path_distance_summable K f h).tsum_le_tsum _
    ((path_distance_summable K f g).add (path_distance_summable K g h))
  intro n
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (truncated_distance_triangle (f.restrict (K n))
    (g.restrict (K n)) (h.restrict (K n))) (by positivity)

theorem compact_stage_distance_measurable
    {Ω D : Type*} [MeasurableSpace Ω] [TopologicalSpace D] [T2Space D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : Ω → C(D,ℝ)) (hX : Measurable X) (hY : Measurable Y) (n : ℕ) :
    Measurable (fun ω => compactStageDist K n (X ω) (Y ω)) := by
  letI : CompactSpace (K n) := isCompact_iff_compactSpace.1 (K.isCompact n)
  have hx : Measurable (fun ω => (X ω).restrict (K n)) :=
    ContinuousMap.measurable_iff_eval.2 (fun x => (ContinuousMap.measurable_eval x.val).comp hX)
  have hy : Measurable (fun ω => (Y ω).restrict (K n)) :=
    ContinuousMap.measurable_iff_eval.2 (fun x => (ContinuousMap.measurable_eval x.val).comp hY)
  exact hx.dist hy

theorem path_distance_measurable
    {Ω D : Type*} [MeasurableSpace Ω] [TopologicalSpace D] [T2Space D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    (K : CompactExhaustion D) (X Y : Ω → C(D,ℝ)) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => pathDistance K (X ω) (Y ω)) := by
  apply Measurable.tsum
  intro n
  exact measurable_const.mul (measurable_const.min (compact_stage_distance_measurable K X Y hX hY n))

end Asakura.Chapter2Complete
#print axioms Asakura.Chapter2Complete.path_distance_bounds
#print axioms Asakura.Chapter2Complete.path_distance_controls_stage
#print axioms Asakura.Chapter2Complete.path_distance_triangle
#print axioms Asakura.Chapter2Complete.compact_stage_distance_measurable
#print axioms Asakura.Chapter2Complete.path_distance_measurable
