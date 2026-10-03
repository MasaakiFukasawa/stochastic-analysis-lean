import Chapter7PathSpaceTopology
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter TopologicalSpace
open scoped NNReal Topology
namespace Asakura.Chapter7

noncomputable def rationalClockGrid (p : ℕ × ℕ) : ℝ≥0 :=
  ⟨(p.2:ℝ)/((p.1:ℝ)+1),by positivity⟩

theorem rational_clock_grid_dense : DenseRange rationalClockGrid := by
  intro t
  let u := fun n : ℕ => (n,⌊(t:ℝ)*((n:ℝ)+1)⌋₊)
  have hl : Tendsto (fun n => rationalClockGrid (u n)) atTop (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    exact (tendsto_nat_floor_mul_div_atTop t.property).comp
      (tendsto_atTop_mono (fun n : ℕ => show (n:ℝ) ≤ (n:ℝ)+1 by linarith) tendsto_natCast_atTop_atTop)
  exact mem_closure_of_tendsto hl (.of_forall (fun n => mem_range_self (u n)))

noncomputable def pathGridValues (f : C(ℝ≥0,ℝ)) : ℕ × ℕ → ℝ :=
  fun p => f (rationalClockGrid p)

/-- Countably many rational grid evaluations determine the actual
continuous path, with its compact-open Borel sigma algebra. -/
theorem path_grid_values_embedding : MeasurableEmbedding pathGridValues := by
  have hm : Measurable pathGridValues := measurable_pi_iff.mpr
    (fun p => ContinuousMap.measurable_eval (rationalClockGrid p))
  apply hm.measurableEmbedding
  intro f g he
  apply ContinuousMap.ext
  exact congrFun (rational_clock_grid_dense.equalizer f.continuous g.continuous (funext (fun p => congrFun he p)))

end Asakura.Chapter7
