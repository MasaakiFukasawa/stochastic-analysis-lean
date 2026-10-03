import FullAuditPathSpaceExercise
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.ContinuousMap.SecondCountableSpace


open Set Filter TopologicalSpace
open scoped NNReal Topology
namespace Asakura.Chapter7

/-- Composition is continuous for the actual compact-open path spaces. -/
theorem clock_composition_continuous :
    Continuous (fun p : C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ≥0) => p.1.comp p.2) :=
  ContinuousMap.continuous_comp'.comp continuous_swap

/-- Every neighborhood of a path contains a condition on one bounded time
interval. This is the topology fact behind the manuscript's series-tail step. -/
theorem path_neighborhood_control (c : C(ℝ≥0,ℝ≥0))
    (U : Set C(ℝ≥0,ℝ≥0)) (hU : U ∈ 𝓝 c) :
    ∃ K : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ f : C(ℝ≥0,ℝ≥0), (∀ t ≤ K,dist (f t) (c t) < ε) → f ∈ U := by
  have hb := nhds_basis_uniformity (x := c)
    ((Metric.uniformity_basis_dist (α := ℝ≥0)).compactConvergenceUniformity (α := ℝ≥0))
  obtain ⟨⟨S,ε⟩,⟨hS,hε⟩,hsub⟩ := hb.mem_iff.mp hU
  obtain ⟨K,hK⟩ := hS.bddAbove
  refine ⟨K,ε,hε,fun f hf => hsub ?_⟩
  intro t ht
  exact hf t (hK ht)

end Asakura.Chapter7
