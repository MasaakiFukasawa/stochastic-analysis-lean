import Chapter12BrownianVectorPathLaw

open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

noncomputable def vectorPathRestriction (d:ℕ) (T:ℝ) (f:Fin d → C(ℝ≥0,ℝ)) : C(Icc (0:ℝ) T,Fin d → ℝ) :=
  ⟨fun t j => f j ⟨t.val,t.property.1⟩,continuous_pi (fun j => (f j).continuous.comp
    (continuous_subtype_val.subtype_mk (fun t:Icc (0:ℝ) T => t.property.1)))⟩

theorem vector_path_restriction_measurable (d:ℕ) (T:ℝ) : Measurable (vectorPathRestriction d T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact Measurable.of_eval (fun j => (ContinuousMap.measurable_eval (⟨t.val,t.property.1⟩ : ℝ≥0)).comp (measurable_pi_apply j))

noncomputable def brownianSystemCompactPath {Ω:Type*} [MeasurableSpace Ω]
    {P:Measure Ω} [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (T:ℝ) : Ω → C(Icc (0:ℝ) T,Fin d → ℝ) :=
  fun w => vectorPathRestriction d T (fun j => brownianCoordinatePath B j w)

theorem brownian_system_compact_measurable {Ω:Type*} [MeasurableSpace Ω]
    {P:Measure Ω} [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (T:ℝ) :
    Measurable (brownianSystemCompactPath B T) :=
  (vector_path_restriction_measurable d T).comp (Measurable.of_eval (brownian_coordinate_path_measurable B))

theorem brownian_compact_common_law {Ω Ω':Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P:Measure Ω) (Q:Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d:ℕ} (B:BrownianSystem P d) (C:BrownianSystem Q d) (T:ℝ) :
    IdentDistrib (brownianSystemCompactPath B T) (brownianSystemCompactPath C T) P Q :=
  (brownian_vector_path_common_law P Q B C).comp (vector_path_restriction_measurable d T)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_compact_common_law
