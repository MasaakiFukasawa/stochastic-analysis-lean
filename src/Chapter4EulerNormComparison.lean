import Chapter4EulerStrongManuscript

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace Asakura.Chapter4
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- Its supremum norm is the squared maximum Euclidean norm of a vector
path. This makes the manuscript's norm explicit. -/
noncomputable def squaredEuclideanPath {D : Type*} [TopologicalSpace D] {dim : ℕ}
    (Y : C(D,Fin dim → ℝ)) : C(D,ℝ) :=
  ⟨fun r => ∑ i,(Y r i)^2,by fun_prop⟩

lemma squared_euclidean_path_bound {D : Type*} [TopologicalSpace D] [CompactSpace D] {dim : ℕ}
    (Y : C(D,Fin dim → ℝ)) : ‖squaredEuclideanPath Y‖≤(dim:ℝ)*‖Y‖^2 := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro r
  change ‖∑ i,(Y r i)^2‖≤_
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have hb i : (Y r i)^2≤‖Y‖^2 := by
    have hh := (norm_le_pi_norm (Y r) i).trans (Y.norm_coe_le_norm r)
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hb i)

lemma squared_euclidean_path_measurable
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D] {dim : ℕ}
    (Y : Ω → C(D,Fin dim → ℝ)) (hY : Measurable Y) :
    Measurable (fun w => squaredEuclideanPath (Y w)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  change Measurable (fun w => ∑ i,(Y w r i)^2)
  exact Finset.measurable_sum Finset.univ fun i _ =>
    ((measurable_pi_apply i).comp ((continuous_eval_const r).measurable.comp hY)).pow_const 2

lemma squared_euclidean_path_expected_bound
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D] {dim : ℕ}
    (P : Measure Ω) (Y : Ω → C(D,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) :
    Integrable (fun w => ‖squaredEuclideanPath (Y w)‖) P ∧
    (∫ w,‖squaredEuclideanPath (Y w)‖ ∂P)≤(dim:ℝ)*(∫ w,‖Y w‖^2 ∂P) := by
  have hm' : AEStronglyMeasurable (fun w => ‖squaredEuclideanPath (Y w)‖) P :=
    (squared_euclidean_path_measurable Y hm).norm.aestronglyMeasurable
  have hdom := (hi.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul (dim:ℝ)
  have hi' : Integrable (fun w => ‖squaredEuclideanPath (Y w)‖) P := hdom.mono' hm'
    (Filter.Eventually.of_forall (fun w => by simpa only [norm_norm] using squared_euclidean_path_bound (Y w)))
  refine ⟨hi',?_⟩
  rw [← integral_const_mul]
  exact integral_mono hi' hdom (fun w => squared_euclidean_path_bound (Y w))

lemma initial_supnorm_moment_le_euclidean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {dim : ℕ}
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P) :
    (∫ w,‖ξ w‖^2 ∂P)≤∫ w,(∑ i,(ξ w i)^2) ∂P := by
  have hi i : Integrable (fun w => (ξ w i)^2) P :=
    (memLp_two_iff_integrable_sq (memLp_pi_iff.mp hξ i).aestronglyMeasurable).mp (memLp_pi_iff.mp hξ i)
  exact integral_mono (hξ.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (integrable_finsetSum Finset.univ (fun i _ => hi i)) (fun w => Asakura.Chapter3Complete.pi_norm_sq_le_sum_sq (ξ w))

lemma euler_euclidean_rate_transfer
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D] {dim : ℕ}
    (P : Measure Ω) (Y : Ω → C(D,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P)
    (ξ : Ω → Fin dim → ℝ) (hξ : MemLp ξ 2 P) (C : ℝ) (hC : 0≤C) (n : ℕ)
    (hb : (∫ w,‖Y w‖^2 ∂P)≤C*(1+∫ w,‖ξ w‖^2 ∂P)/(n:ℝ)) :
    (∫ w,‖squaredEuclideanPath (Y w)‖ ∂P)≤
      ((dim:ℝ)*C)*(1+∫ w,(∑ i,(ξ w i)^2) ∂P)/(n:ℝ) := by
  have h₁ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg dim)
  have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (1:ℝ)) (initial_supnorm_moment_le_euclidean P ξ hξ)) hC) (Nat.cast_nonneg n)
  have h₃ := mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg dim)
  have hh := (squared_euclidean_path_expected_bound P Y hm hi).2.trans (h₁.trans h₃)
  convert hh using 1 <;> ring

end Asakura.Chapter4
