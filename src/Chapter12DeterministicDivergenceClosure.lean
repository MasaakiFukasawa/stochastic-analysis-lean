import Chapter12DivergenceClosureCompatibility

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Deterministic divergence passes directly from the constructed cylinder
operator to its closure, without reconstructing a second derivative operator. -/
theorem deterministic_divergence_closure_from_core {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P) (hc : D.IsClosable)
    (hgraph : (D.graph : Set _)=range (cylinderPair P W S hS hcore 2 (by simp)))
    (h : H) : IsDivergence D.closure ((memLp_const (μ := P) (p := 2) h).toLp (fun _ => h)) (W h) := by
  have hg : D.graph=Submodule.span ℝ (range (cylinderPair P W S hS hcore 2 (by simp))) := by
    apply SetLike.coe_injective
    rw [cylinderPair_span_eq_range]
    exact hgraph
  have he : (D.closure.graph : Set (Lp ℝ 2 P × Lp H 2 P))=closure (D.graph : Set (Lp ℝ 2 P × Lp H 2 P)) := by
    rw [←hc.graph_closure_eq_closure_graph,Submodule.topologicalClosure_coe]
  exact (divergence_unchanged_by_graph_closure D D.closure he _ _).mpr
    (deterministic_divergence_on_cylinder_graph P W S hS hcore D hg h)

end Asakura.Chapter12
