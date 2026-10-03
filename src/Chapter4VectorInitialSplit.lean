import Chapter4VectorPrefixMoment
import Chapter4FiniteSumPathMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4.Vector
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

lemma vector_constant_path_memLp
    {Ω D : Type*} [MeasurableSpace Ω] [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    {dim : ℕ} (P : Measure Ω) (ξ : Ω → Fin dim → ℝ) (hm : Measurable ξ) (hi : MemLp ξ 2 P) :
    MemLp (fun w => ContinuousMap.const D (ξ w)) 2 P := by
  have hcm : Measurable (fun w => ContinuousMap.const D (ξ w)) := ContinuousMap.measurable_iff_eval.mpr (fun _ => hm)
  apply hi.of_le_mul (c:=1) hcm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w => by simpa only [one_mul] using
    (ContinuousMap.norm_le _ (norm_nonneg (ξ w))).mpr (fun _ => le_rfl))

lemma prefix_path_memLp
    {Ω : Type*} [MeasurableSpace Ω] {dim : ℕ} (P : Measure Ω) (R : ℝ) (hR : 0≤R)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P) (t : ℝ) :
    MemLp (fun w => prefixPath hR (Y w) t) 2 P := by
  apply hi.of_le_mul (c:=1) (prefix_path_measurable hR Y hm t).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w => by simpa only [one_mul] using prefix_path_norm_le hR (Y w) t)

lemma initial_split_prefix_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {dim : ℕ} (P : Measure Ω) (R : ℝ) (hR : 0≤R)
    (Y : Ω → C(Icc (0:ℝ) R,Fin dim → ℝ)) (hm : Measurable Y) (hi : MemLp Y 2 P)
    (ξ : Ω → Fin dim → ℝ) (hξm : Measurable ξ) (hξi : MemLp ξ 2 P) (t : ℝ) :
    (∫ w,‖prefixPath hR (Y w) t‖^2 ∂P)≤2*(∫ w,‖ξ w‖^2 ∂P)+
      2*(∫ w,‖prefixPath hR (Y w-ContinuousMap.const (Icc (0:ℝ) R) (ξ w)) t‖^2 ∂P) := by
  let J := fun w => ContinuousMap.const (Icc (0:ℝ) R) (ξ w)
  have hJm : Measurable J := ContinuousMap.measurable_iff_eval.mpr (fun _ => hξm)
  have hJi : MemLp J 2 P := vector_constant_path_memLp P ξ hξm hξi
  let Q := fun w => prefixPath hR (Y w-J w) t
  have hQi : MemLp Q 2 P := prefix_path_memLp P R hR _ (hm.sub hJm) (hi.sub hJi) t
  have he : ∀ w,J w+Q w=prefixPath hR (Y w) t := by
    intro w
    ext r i
    simp only [ContinuousMap.add_apply,Q,prefixPath,ContinuousMap.coe_mk,ContinuousMap.sub_apply,J,ContinuousMap.const_apply,Pi.add_apply,Pi.sub_apply]
    ring
  have hb := (Asakura.Chapter4.path_sum_square_moment P J Q hJi hQi).2
  simp_rw [he] at hb
  have hJbound : (∫ w,‖J w‖^2 ∂P)≤∫ w,‖ξ w‖^2 ∂P := by
    apply integral_mono (hJi.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (hξi.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    intro w
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun _ => le_rfl)
  linarith only [hb,hJbound]

end Asakura.Chapter4.Vector
