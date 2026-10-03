import Chapter7BrownianGridSamples
import Chapter7PathGridEmbedding
import Chapter7ClockHalfTime
import Mathlib.Probability.Process.FiniteDimensionalLaws

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

lemma finite_clock_grid_common_denominator {ι : Type*} [Fintype ι] (p : ι → ℕ × ℕ) :
    ∃ D : ℕ,0 < D ∧ ∃ k : ι → ℕ,∀ i,
      (rationalClockGrid (p i):ℝ) = (k i:ℝ)/(D:ℝ) := by
  classical
  let D := ∏ i,((p i).1+1)
  have hD : 0 < D := by
    dsimp only [D]
    exact Finset.prod_pos (fun i _ => Nat.succ_pos _)
  have hdiv i : (p i).1+1 ∣ D := Finset.dvd_prod_of_mem (fun i => (p i).1+1) (Finset.mem_univ i)
  refine ⟨D,hD,fun i => (p i).2*(D/((p i).1+1)),?_⟩
  intro i
  change ((p i).2:ℝ)/((p i).1+1:ℝ) = ((p i).2*(D/((p i).1+1)):ℕ)/(D:ℝ)
  rw [Nat.cast_mul,Nat.cast_div_charZero (hdiv i),Nat.cast_add,Nat.cast_one]
  field_simp
  <;> push_cast
  <;> ring

noncomputable def brownianContinuousPath
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) (w : Ω) : C(ℝ≥0,ℝ) :=
  ⟨fun t => B.W 0 (realTimeClamp t) w,continuous_iff_continuousAt.mpr (fun t =>
    (((B.martingale 0).path P B.F w _ (changed_time_finite t t.property)).comp
      real_time_clamp_continuous.continuousAt).comp NNReal.continuous_coe.continuousAt)⟩

lemma brownian_continuous_path_measurable
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSystem P 1) : Measurable[m] (brownianContinuousPath B) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((B.martingale 0).adapted P B.F _ (changed_time_finite t t.property)).mono (B.le _) le_rfl

/-- Equality of Brownian laws on the actual continuous path space follows
from the previously proved joint increment laws. No common path law is
assumed for the DDS Brownian motions in the functional CLT. -/
theorem brownian_continuous_path_common_law
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (B B0 : BrownianSystem P 1) :
    IdentDistrib (brownianContinuousPath B) (brownianContinuousPath B0) P P := by
  have hm := brownian_continuous_path_measurable B
  have hm0 := brownian_continuous_path_measurable B0
  have he : IdentDistrib (fun w => pathGridValues (brownianContinuousPath B w))
      (fun w => pathGridValues (brownianContinuousPath B0 w)) P P := by
    apply (identDistrib_iff_forall_finset_identDistrib
      (path_grid_values_embedding.measurable.comp hm).aemeasurable
      (path_grid_values_embedding.measurable.comp hm0).aemeasurable).mpr
    intro I
    obtain ⟨D,hD,k,hk⟩ := finite_clock_grid_common_denominator (fun i : I => i.val)
    have hl := brownian_grid_samples_law P B B0 (1/(D:ℝ)) (by positivity) k
    convert hl using 1 <;> funext w i <;>
      simp only [Function.comp_def,Finset.restrict, pathGridValues,brownianContinuousPath,ContinuousMap.coe_mk,hk i,div_eq_mul_inv,one_div,one_mul]
  refine ⟨hm.aemeasurable,hm0.aemeasurable,?_⟩
  apply path_grid_values_embedding.map_injective
  rw [Measure.map_map path_grid_values_embedding.measurable hm,
    Measure.map_map path_grid_values_embedding.measurable hm0]
  exact he.map_eq

end Asakura.Chapter7
