import Chapter4VectorPrefixMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1500000

lemma random_path_evaluation_memLp
    {Ω D E : Type*} [MeasurableSpace Ω] [TopologicalSpace D] [CompactSpace D]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (V : Ω → C(D,E)) (hm : Measurable V) (hi : MemLp V 2 P) (r : D) :
    MemLp (fun w => V w r) 2 P := by
  apply hi.norm.mono' ((continuous_eval_const r).measurable.comp hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun w => (V w).norm_coe_le_norm r)

lemma random_path_evaluation_square_moment
    {Ω D E : Type*} [MeasurableSpace Ω] [TopologicalSpace D] [CompactSpace D]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (V : Ω → C(D,E)) (hm : Measurable V) (hi : MemLp V 2 P) (r : D) :
    (∫ w,‖V w r‖^2 ∂P)≤∫ w,‖V w‖^2 ∂P := by
  apply integral_mono
    ((random_path_evaluation_memLp P V hm hi r).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    (hi.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
  exact fun w => pow_le_pow_left₀ (norm_nonneg _) ((V w).norm_coe_le_norm r) 2

end Asakura.Chapter4
