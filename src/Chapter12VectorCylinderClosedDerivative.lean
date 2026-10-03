import Chapter12TensorCylinderPairs

open MeasureTheory ProbabilityTheory Set ENNReal
open TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A single construction works for H-valued and higher-tensor-valued
cylinders. The domain is the finite linear span, and closure is taken only
after proving closability by Gaussian duality. -/
theorem vector_cylinder_closed_derivative {Ω H E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H] [SeparableSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SeparableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) :
    ∃ D : Lp E p P →ₗ.[ℝ] Lp (CompletedHilbertTensor H E) p P,
      D.graph=Submodule.span ℝ (range (fun z : SmoothCylinder H × E =>
        (vectorCylinderValue P W S hS hcore z.1 z.2 p hp,
         vectorCylinderDerivative P W S hS hcore z.1 z.2 p hp))) ∧
      D.IsClosable ∧ D.closure.IsClosed ∧
      ∀ c : SmoothCylinder H,∀ e : E,
        (vectorCylinderValue P W S hS hcore c e p hp,
         vectorCylinderDerivative P W S hS hcore c e p hp)∈D.closure.graph := by
  classical
  let tests := range (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)
  let select (v : tests) : SmoothCylinder H := v.property.choose
  have hselect (v : tests) : (select v).valueLp P W S hS hcore q hq=v.val := v.property.choose_spec
  have hop := tensor_Lp_operator_from_cylinder_pairs P p q
    (fun z : SmoothCylinder H × E => vectorCylinderValue P W S hS hcore z.1 z.2 p hp)
    (fun z : SmoothCylinder H × E => vectorCylinderDerivative P W S hS hcore z.1 z.2 p hp)
    tests hdense (fun v h => (select v).ibpTestLp P W S hS hcore h q hq) (by
      intro z v h e
      rw [← hselect v]
      exact vector_cylinder_ibp P W S hS hcore z.1 (select v) z.2 e h p q hp hq)
  obtain ⟨D,hgraph,hclos,hcoreD⟩ := hop
  refine ⟨D,hgraph,hclos,?_,?_⟩
  · exact hclos.closure_isClosed
  · intro c e
    rw [← hclos.graph_closure_eq_closure_graph]
    exact D.graph.le_topologicalClosure (hcoreD (c,e))

end Asakura.Chapter12
