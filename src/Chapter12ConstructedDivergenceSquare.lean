import Chapter12VectorDivergenceSquareBound
import Chapter12VectorCoreSpan
import Chapter12DivergenceSquareClosure

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

/-- Construction of the D^{1,2}(H) derivative and the full divergence
extension, including the square bound, from the same Wiener cylinder data. -/
theorem constructed_divergence_square_extension {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (D₀ : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hgraph : (D₀.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore 2 (by simp))) :
    ∃ D₁ : Lp H 2 P →ₗ.[ℝ] Lp (CompletedHilbertTensor H H) 2 P,
      D₁.IsClosed ∧
      (D₁.graph : Set _)=closure (range (vectorExprPair (E:=H) P W S hS hcore 2 (by simp))) ∧
      ∀ u : D₁.domain,∃ z : Lp ℝ 2 P,
        IsDivergence D₀ (u : Lp H 2 P) z ∧ ‖z‖^2≤‖(u : Lp H 2 P)‖^2+‖D₁ u‖^2 := by
  obtain ⟨A,hA,hclos,hclosed,hterm⟩ := vector_cylinder_closed_derivative (E:=H)
    P W S hS hcore 2 2 (by simp) (by simp) hdense
  have hdom (c : SmoothCylinder H) : c.valueLp P W S hS hcore 2 (by simp)∈D₀.domain := by
    have hh : cylinderPair P W S hS hcore 2 (by simp) c∈D₀.graph := by
      change cylinderPair P W S hS hcore 2 (by simp) c∈(D₀.graph : Set _)
      rw [hgraph]
      exact subset_closure (mem_range_self c)
    obtain ⟨f,hf,_⟩ := D₀.mem_graph_iff.mp hh
    change (f : Lp ℝ 2 P)=c.valueLp P W S hS hcore 2 (by simp) at hf
    rw [← hf]
    exact f.property
  have hdD : DenseRange (fun f : D₀.domain => (f : Lp ℝ 2 P)) := by
    apply hdense.mono
    rintro _ ⟨c,rfl⟩
    exact ⟨⟨_,hdom c⟩,rfl⟩
  have hrange : (A.graph : Set _)=range (vectorExprPair (E:=H) P W S hS hcore 2 (by simp)) := by
    rw [hA]
    exact vector_core_span_range P W S hS hcore 2 (by simp)
  have hbound : ∀ a∈A.graph,∃ z,IsDivergence D₀ a.1 z ∧ ‖z‖^2≤‖a.1‖^2+‖a.2‖^2 := by
    intro a ha
    change a∈(A.graph : Set _) at ha
    rw [hrange] at ha
    obtain ⟨c,rfl⟩ := ha
    obtain ⟨g,hg,hb⟩ := vector_cylinder_divergence_square_bound H P W S hS hcore D₀ hgraph hdense c
    refine ⟨g.valueLp P W S hS hcore 2 (by simp),hg,?_⟩
    simpa only [vectorExprPair,vector_cylinder_differentiate_value] using hb
  refine ⟨A.closure,hclosed,?_,fun u => ?_⟩
  · rw [← hclos.graph_closure_eq_closure_graph]
    exact congrArg closure hrange
  · have hu : ((u : Lp H 2 P),A.closure u)∈A.graph.topologicalClosure := by
      rw [hclos.graph_closure_eq_closure_graph]
      exact A.closure.mem_graph u
    exact divergence_square_on_graph_closure D₀ hdD A.graph hbound _ hu

end Asakura.Chapter12
