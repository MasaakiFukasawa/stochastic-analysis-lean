import Chapter7PathSpaceTopology
import Mathlib.Topology.Metrizable.Uniformity

open Set Filter
open scoped Topology NNReal Uniformity
namespace Asakura.Chapter7

/-- Agreement on growing initial intervals makes pairs of paths uniformly
close in the compact-convergence uniformity, even when both paths vary. -/
theorem path_prefix_uniformity
    (U : Set (C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ))) (hU : U ∈ 𝓤 C(ℝ≥0,ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f g : C(ℝ≥0,ℝ),
      (∀ t : ℝ≥0,t ≤ n → f t = g t) → (f,g) ∈ U := by
  have hb := (Metric.uniformity_basis_dist (α := ℝ)).compactConvergenceUniformity (α := ℝ≥0)
  obtain ⟨⟨S,ε⟩,⟨hS,hε⟩,hsub⟩ := hb.mem_iff.mp hU
  obtain ⟨K,hK⟩ := hS.bddAbove
  obtain ⟨N,hN⟩ := exists_nat_ge K
  refine ⟨N,fun n hn f g he => hsub ?_⟩
  intro t ht
  have htn : t ≤ (n:ℝ≥0) := le_trans (hK ht) (le_trans hN (by exact_mod_cast hn))
  change dist (f t) (g t) < ε
  simpa only [he t htn,dist_self] using hε

end Asakura.Chapter7
