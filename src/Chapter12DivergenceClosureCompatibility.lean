import Chapter12DivergenceClosedGraph
import Chapter12DeterministicDivergence
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem divergence_unchanged_by_graph_closure
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (D₀ D : E →ₗ.[ℝ] H) (hgraph : (D.graph : Set (E × H)) = closure (D₀.graph : Set (E × H)))
    (u : H) (z : E) : IsDivergence D u z ↔ IsDivergence D₀ u z := by
  have htest (A : E →ₗ.[ℝ] H) : IsDivergence A u z ↔
      ∀ a ∈ (A.graph : Set (E × H)), ⟪a.2,u⟫ = ⟪a.1,z⟫ := by
    constructor
    · intro h a ha
      rcases (A.mem_graph_iff).mp ha with ⟨f,hf,hDf⟩
      rw [←hf,←hDf]
      exact h f
    · intro h f
      exact h _ (A.mem_graph f)
  rw [htest D,htest D₀,hgraph]
  constructor
  · intro h a ha
    exact h a (subset_closure ha)
  · intro h a ha
    exact (closure_minimal h (isClosed_eq (by fun_prop) (by fun_prop))) ha

theorem deterministic_divergence_on_closed_graph
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [CompleteSpace H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore 2 (by simp)))
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (h : H) : IsDivergence D ((memLp_const (μ := P) (p := 2) h).toLp (fun _ => h)) (W h) := by
  obtain ⟨D₀,hg,hclose,hc⟩ := concrete_cylinder_operator P W S hS hcore 2 2 (by simp) (by simp) hdense
  have he : (D.graph : Set (Lp ℝ 2 P × Lp H 2 P)) = closure (D₀.graph : Set (Lp ℝ 2 P × Lp H 2 P)) := by
    rw [hg]
    change (D.graph : Set (Lp ℝ 2 P × Lp H 2 P)) = closure (Submodule.span ℝ (range (cylinderPair P W S hS hcore 2 (by simp))) : Set (Lp ℝ 2 P × Lp H 2 P))
    rw [cylinderPair_span_eq_range]
    exact hgraph
  exact (divergence_unchanged_by_graph_closure D₀ D he _ _).mpr
    (deterministic_divergence_on_cylinder_graph P W S hS hcore D₀ hg h)

end Asakura.Chapter12
