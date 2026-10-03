import Chapter12BrownianGridCommonLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter12
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter7
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem finite_coordinates_identDistrib {Ω Ω' I:Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P:Measure Ω) (Q:Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X:Ω → I → ℝ) (Y:Ω' → I → ℝ) (hX:AEMeasurable X P) (hY:AEMeasurable Y Q)
    (h:∀J:Finset I,IdentDistrib (fun w => J.restrict (X w)) (fun w => J.restrict (Y w)) P Q) :
    IdentDistrib X Y P Q := by
  have hx := isProjectiveLimit_map hX
  have he J := (h J).map_eq
  simp_rw [he] at hx
  exact ⟨hX,hY,hx.unique (isProjectiveLimit_map hY)⟩

noncomputable def brownianCoordinatePath {Ω:Type*} [MeasurableSpace Ω]
    {P:Measure Ω} [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (j:Fin d) (w:Ω) : C(ℝ≥0,ℝ) :=
  ⟨fun t => B.W j (realTimeClamp t) w,continuous_iff_continuousAt.mpr (fun t =>
    (((B.martingale j).path P B.F w _ (Asakura.Chapter7.changed_time_finite t t.property)).comp
      real_time_clamp_continuous.continuousAt).comp NNReal.continuous_coe.continuousAt)⟩

theorem brownian_coordinate_path_measurable {Ω:Type*} [MeasurableSpace Ω]
    {P:Measure Ω} [IsProbabilityMeasure P] {d:ℕ} (B:BrownianSystem P d) (j:Fin d) :
    Measurable (brownianCoordinatePath B j) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((B.martingale j).adapted P B.F _ (Asakura.Chapter7.changed_time_finite t t.property)).mono (B.le _) le_rfl

noncomputable def vectorPathGrid {d:ℕ} (f:Fin d → C(ℝ≥0,ℝ)) : Fin d×(ℕ×ℕ) → ℝ :=
  fun z => f z.1 (rationalClockGrid z.2)

theorem vector_path_grid_embedding (d:ℕ) : MeasurableEmbedding (vectorPathGrid (d:=d)) := by
  have hm:Measurable (vectorPathGrid (d:=d)) := Measurable.of_eval (fun z =>
    (ContinuousMap.measurable_eval (rationalClockGrid z.2)).comp (measurable_pi_apply z.1))
  apply hm.measurableEmbedding
  intro f g he
  funext j
  apply path_grid_values_embedding.injective
  funext z
  exact congrFun he (j,z)

theorem brownian_vector_path_common_law {Ω Ω':Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P:Measure Ω) (Q:Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {d:ℕ} (B:BrownianSystem P d) (C:BrownianSystem Q d) :
    IdentDistrib (fun w j => brownianCoordinatePath B j w)
      (fun w j => brownianCoordinatePath C j w) P Q := by
  have hm:Measurable (fun w j => brownianCoordinatePath B j w) :=
    Measurable.of_eval (brownian_coordinate_path_measurable B)
  have hm':Measurable (fun w j => brownianCoordinatePath C j w) :=
    Measurable.of_eval (brownian_coordinate_path_measurable C)
  have he:IdentDistrib (fun w => vectorPathGrid (fun j => brownianCoordinatePath B j w))
      (fun w => vectorPathGrid (fun j => brownianCoordinatePath C j w)) P Q := by
    apply finite_coordinates_identDistrib P Q _ _
      ((vector_path_grid_embedding d).measurable.comp hm).aemeasurable
      ((vector_path_grid_embedding d).measurable.comp hm').aemeasurable
    intro I
    obtain ⟨D,hD,k,hk⟩ := finite_clock_grid_common_denominator (fun i:I => i.val.2)
    have hl := brownian_grid_common_law P Q B C (1/(D:ℝ)) (by positivity) k (fun i:I => i.val.1)
    convert hl using 1 <;> funext w i <;>
      simp only [Function.comp_def,Finset.restrict,vectorPathGrid,brownianCoordinatePath,ContinuousMap.coe_mk,
        hk i,div_eq_mul_inv,one_div,one_mul]
  refine ⟨hm.aemeasurable,hm'.aemeasurable,?_⟩
  apply (vector_path_grid_embedding d).map_injective
  rw [Measure.map_map (vector_path_grid_embedding d).measurable hm,
    Measure.map_map (vector_path_grid_embedding d).measurable hm']
  exact he.map_eq
end Asakura.Chapter12
#print axioms Asakura.Chapter12.brownian_vector_path_common_law
