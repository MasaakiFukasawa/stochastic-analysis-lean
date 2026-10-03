import Chapter12ClosedCylinderGraphFromData
import Chapter12DivergenceClosedGraph

open MeasureTheory ProbabilityTheory Set ENNReal
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The divergence is constructed for the same closed derivative obtained
from the Wiener data; its dense-domain premise is proved from cylinders. -/
theorem divergence_from_wiener_data {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [SecondCountableTopology H] [CompleteSpace H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t,Measurable (X t))
    (hXc : ∀ w,Continuous (fun t => X t w))
    (h : K → H) (hXW : ∀ t,X t=ᵐ[P] (W (h t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (hgen : ∀ f : Lp ℝ 2 P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) :
    ∃ D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P,
      D.IsClosed ∧ (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))) ∧
      (divergenceOperator D).IsClosed ∧
      (∀ u z,(u,z)∈(divergenceOperator D).graph ↔ IsDivergence D u z) ∧
      ∀ u,(∃ z,IsDivergence D u z) ↔
        ∃ C : ℝ,∀ f : D.domain,|inner ℝ (D f) u|≤C*‖(f : Lp ℝ 2 P)‖ := by
  obtain ⟨D,hclosed,hgraph⟩ := closed_cylinder_graph_from_data P W S hS hcore
    X hXm hXc h hXW times htimes 2 2 (by simp) (by simp) hgen
  have hd := concrete_cylinder_dense P W S hS hcore X hXm hXc h hXW times htimes 2 (by simp) hgen
  have hdom (c : SmoothCylinder H) : c.valueLp P W S hS hcore 2 (by simp)∈D.domain := by
    have hc : cylinderPair P W S hS hcore 2 (by simp) c∈D.graph := by
      change cylinderPair P W S hS hcore 2 (by simp) c∈(D.graph : Set _)
      rw [hgraph]
      exact subset_closure (mem_range_self c)
    obtain ⟨f,hf,_⟩ := D.mem_graph_iff.mp hc
    change (f : Lp ℝ 2 P)=c.valueLp P W S hS hcore 2 (by simp) at hf
    rw [←hf]
    exact f.property
  have hdD : DenseRange (fun f : D.domain => (f : Lp ℝ 2 P)) := by
    apply hd.mono
    rintro _ ⟨c,rfl⟩
    exact ⟨⟨_,hdom c⟩,rfl⟩
  refine ⟨D,hclosed,hgraph,divergence_operator_closed D hdD,?_,?_⟩
  · intro u z
    rw [divergence_operator_graph D hdD]
    rfl
  · exact divergence_domain_iff D hdD

end Asakura.Chapter12
