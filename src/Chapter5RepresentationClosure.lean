import Mathlib.Analysis.Normed.Operator.LinearIsometry
import FullAuditChapter5Estimates

open Set Filter
open scoped Topology
namespace Asakura.Chapter5

/-- The passage from representable smooth cylinders to arbitrary L2 variables.
The map here must be the isometric stochastic-integral map; density and that
identification are separate analytic obligations. -/
theorem representation_of_dense_isometry {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : H →ₗᵢ[ℝ] E) (S : Set E) (hS : Dense S)
    (hrep : S ⊆ range I) : Function.Surjective I := by
  have hc : IsClosed (range I) := I.isometry.isClosedEmbedding.isClosed_range
  have he : closure S ⊆ range I := closure_minimal hrep hc
  intro x
  exact he (hS x)

/-- A terminal payoff approximation determines a unique integrand limit.
Unlike a purely algebraic coefficient check, this constructs the limit in H. -/
theorem integrand_limit_from_terminal_limit {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : H →ₗᵢ[ℝ] E) (h : ℕ → H) (X : E)
    (hlim : Tendsto (fun n => I (h n)) atTop (𝓝 X)) :
    ∃! u, I u = X := by
  have hc : IsClosed (range I) := I.isometry.isClosedEmbedding.isClosed_range
  have hm : X ∈ range I := hc.mem_of_tendsto hlim (Eventually.of_forall (fun n => ⟨h n,rfl⟩))
  obtain ⟨u,hu⟩ := hm
  refine ⟨u,hu,?_⟩
  intro v hv
  exact I.injective (hv.trans hu.symm)

end Asakura.Chapter5
