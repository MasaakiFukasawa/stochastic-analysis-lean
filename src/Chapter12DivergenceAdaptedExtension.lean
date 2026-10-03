import Chapter12DivergenceClosedGraph
import Chapter12BrownianTimeSurjective

open Set
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Equality on the dense adapted step core extends to every finite-energy
integrand, using the closed duality relation and the Ito isometry. -/
theorem divergence_from_adapted_step_core {E H K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (D : E →ₗ.[ℝ] H) (J : K →L[ℝ] H) (I : K →L[ℝ] E)
    (S : Set K) (hS : Dense (Submodule.span ℝ S : Set K))
    (hcore : ∀ v∈S,IsDivergence D (J v) (I v)) :
    ∀ v,IsDivergence D (J v) (I v) := by
  let A := (divergenceGraph D).comap (J.prod I).toLinearMap
  have hs : Submodule.span ℝ S≤A := Submodule.span_le.mpr hcore
  have hc : IsClosed (A : Set K) := (divergence_graph_isClosed D).preimage (J.prod I).continuous
  intro v
  exact closure_minimal hs hc (hS v)

/-- The identification with an independently constructed Ito operator is
unique as soon as both constructions agree with actual bounded steps. -/
theorem ito_extension_unique_on_steps {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (I J : K →L[ℝ] E) (S : Set K) (hS : Dense (Submodule.span ℝ S : Set K))
    (hstep : ∀ v∈S,I v=J v) : I=J := by
  apply ContinuousLinearMap.ext_on hS
  exact hstep

end Asakura.Chapter12
