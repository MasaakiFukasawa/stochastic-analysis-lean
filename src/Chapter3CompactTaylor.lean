import Chapter3WrittenMultivariate
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Convex.Basic

open Set Filter
open scoped Topology
namespace Asakura.Chapter3Complete
open Asakura.Chapter3Written

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The uniform Hessian estimate used in the multidimensional Ito proof.
It follows from C2 and compactness, rather than being an additional premise. -/
theorem compact_hessian_uniform_bound {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {K : Set E} (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, ‖x-y‖ ≤ δ →
      ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y‖ ≤ ε := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by norm_num)
  simpa only [dist_eq_norm] using Metric.uniformContinuousOn_iff_le.mp
    (hK.uniformContinuousOn_of_continuous h2.continuous.continuousOn) ε hε

/-- On the compact convex set containing the path and its chords, the Taylor
remainder is uniformly small relative to the squared increment. -/
theorem compact_uniform_taylor {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ v : E, x+v ∈ K → ‖v‖ ≤ δ →
      |f (x+v)-f x-(fderiv ℝ f x) v-
        (fderiv ℝ (fderiv ℝ f) x) v v/2| ≤ ε*‖v‖^2/2 := by
  obtain ⟨δ,hδ,huniform⟩ := compact_hessian_uniform_bound hf hK ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx v hxv hv
  apply multivariate_taylor_remainder hf x v hε.le
  intro t ht
  apply huniform (x+t • v) (hconv.add_smul_mem hx hxv ht) x hx
  calc
    ‖x+t • v-x‖ = t*‖v‖ := by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    _ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ ≤ δ := by simpa using hv

end Asakura.Chapter3Complete
#print axioms Asakura.Chapter3Complete.compact_hessian_uniform_bound
#print axioms Asakura.Chapter3Complete.compact_uniform_taylor
