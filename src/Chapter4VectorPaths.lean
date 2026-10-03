import Chapter4PathMoment
import Chapter3FiniteDimensionalTaylor
import FullAuditPathSpaceExercise

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
open Asakura.Chapter3Complete
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

noncomputable def bundleRealPaths {D : Type*} [TopologicalSpace D] {n : ℕ}
    (Y : Fin n → C(D,ℝ)) : C(D,Fin n → ℝ) :=
  ⟨fun t i => Y i t,continuous_pi (fun i => (Y i).continuous)⟩

noncomputable def coordinateRealPath {D : Type*} [TopologicalSpace D] {n : ℕ}
    (Y : C(D,Fin n → ℝ)) (i : Fin n) : C(D,ℝ) :=
  ⟨fun t => Y t i,(continuous_apply i).comp Y.continuous⟩

lemma coordinate_path_norm_le {D : Type*} [TopologicalSpace D] [CompactSpace D] {n : ℕ}
    (Y : C(D,Fin n → ℝ)) (i : Fin n) : ‖coordinateRealPath Y i‖≤‖Y‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  exact (norm_le_pi_norm (Y t) i).trans (ContinuousMap.norm_coe_le_norm Y t)

lemma bundle_path_norm_le_sum {D : Type*} [TopologicalSpace D] [CompactSpace D] {n : ℕ}
    (Y : Fin n → C(D,ℝ)) : ‖bundleRealPaths Y‖≤∑ i,‖Y i‖ := by
  have hp : 0≤∑ i,‖Y i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply (ContinuousMap.norm_le _ hp).2
  intro t
  apply (pi_norm_le_iff_of_nonneg hp).2
  intro i
  exact (ContinuousMap.norm_coe_le_norm (Y i) t).trans
    (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i))

lemma bundle_path_square_le_sum {D : Type*} [TopologicalSpace D] [CompactSpace D] {n : ℕ}
    (Y : Fin n → C(D,ℝ)) : ‖bundleRealPaths Y‖^2≤∑ i,‖Y i‖^2 := by
  have hn : ‖bundleRealPaths Y‖≤‖(fun i => ‖Y i‖)‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    exact (ContinuousMap.norm_coe_le_norm (Y i) t).trans
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using norm_le_pi_norm (fun j => ‖Y j‖) i)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (pi_norm_sq_le_sum_sq (fun i => ‖Y i‖))

lemma bundle_path_measurable
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    {n : ℕ} (Y : Fin n → Ω → C(D,ℝ)) (hm : ∀ i,Measurable (Y i)) :
    Measurable (fun w => bundleRealPaths (fun i => Y i w)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  apply measurable_pi_iff.mpr
  intro i
  exact (continuous_eval_const t).measurable.comp (hm i)

lemma coordinate_path_measurable
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    {n : ℕ} (Y : Ω → C(D,Fin n → ℝ)) (hm : Measurable Y) (i : Fin n) :
    Measurable (fun w => coordinateRealPath (Y w) i) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (measurable_pi_apply i).comp ((continuous_eval_const t).measurable.comp hm)

lemma bundle_path_memLp
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) {n : ℕ} (Y : Fin n → Ω → C(D,ℝ))
    (hm : ∀ i,Measurable (Y i)) (hi : ∀ i,MemLp (Y i) 2 P) :
    MemLp (fun w => bundleRealPaths (fun i => Y i w)) 2 P := by
  have hs : MemLp (fun w => ∑ i,‖Y i w‖) 2 P := by
    convert memLp_finsetSum' Finset.univ (fun i _ => (hi i).norm) using 1
    ext w
    simp
  apply hs.of_le_mul (c := 1) (bundle_path_measurable Y hm).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro w
  simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] using
    bundle_path_norm_le_sum (fun i => Y i w)

lemma coordinate_path_memLp
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) {n : ℕ} (Y : Ω → C(D,Fin n → ℝ))
    (hm : Measurable Y) (hi : MemLp Y 2 P) (i : Fin n) :
    MemLp (fun w => coordinateRealPath (Y w) i) 2 P := by
  apply hi.of_le_mul (c := 1) (coordinate_path_measurable Y hm i).aestronglyMeasurable
  exact .of_forall (fun w => by simpa only [one_mul] using coordinate_path_norm_le (Y w) i)

lemma bundle_path_second_moment
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    (P : Measure Ω) {n : ℕ} (Y : Fin n → Ω → C(D,ℝ))
    (hm : ∀ i,Measurable (Y i)) (hi : ∀ i,MemLp (Y i) 2 P) :
    (∫ w,‖bundleRealPaths (fun i => Y i w)‖^2 ∂P)≤∑ i,∫ w,‖Y i w‖^2 ∂P := by
  rw [← integral_finsetSum Finset.univ (fun i _ => (hi i).integrable_norm_pow (by norm_num : (2:ℕ)≠0))]
  apply integral_mono ((bundle_path_memLp P Y hm hi).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (integrable_finsetSum Finset.univ (fun i _ => (hi i).integrable_norm_pow (by norm_num : (2:ℕ)≠0)))
  exact fun w => bundle_path_square_le_sum (fun i => Y i w)

end Asakura.Chapter4
