import Chapter4VectorPaths
import Chapter4PrefixPowerMoment

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Asakura.Chapter4
set_option maxHeartbeats 1300000

noncomputable def normEnvelope {D E : Type*} [TopologicalSpace D] [NormedAddCommGroup E]
    (Y : C(D,E)) : C(D,ℝ) := ⟨fun t => ‖Y t‖,Y.continuous.norm⟩

lemma norm_envelope_norm {D E : Type*} [TopologicalSpace D] [CompactSpace D]
    [NormedAddCommGroup E] (Y : C(D,E)) : ‖normEnvelope Y‖=‖Y‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    simpa only [normEnvelope,ContinuousMap.coe_mk,Real.norm_eq_abs,abs_norm] using ContinuousMap.norm_coe_le_norm Y t
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    simpa only [normEnvelope,ContinuousMap.coe_mk,Real.norm_eq_abs,abs_norm] using ContinuousMap.norm_coe_le_norm (normEnvelope Y) t

lemma norm_envelope_measurable {Ω D E : Type*} [MeasurableSpace Ω]
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Y : Ω → C(D,E)) (hm : Measurable Y) : Measurable (fun w => normEnvelope (Y w)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((continuous_eval_const t).measurable.comp hm).norm

lemma norm_envelope_memLp {Ω D E : Type*} [MeasurableSpace Ω]
    [MetricSpace D] [CompactSpace D] [SecondCountableTopology D]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Y : Ω → C(D,E)) (hm : Measurable Y) (p : ℝ≥0∞) :
    MemLp (fun w => normEnvelope (Y w)) p P ↔ MemLp Y p P := by
  constructor
  · intro hi
    apply hi.of_le_mul (c := 1) hm.aestronglyMeasurable
    exact .of_forall (fun w => by simp only [one_mul,norm_envelope_norm,le_refl])
  · intro hi
    apply hi.of_le_mul (c := 1) (norm_envelope_measurable Y hm).aestronglyMeasurable
    exact .of_forall (fun w => by simp only [one_mul,norm_envelope_norm,le_refl])

end Asakura.Chapter4
