import Chapter12ClosedCylinderGraphFromData

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace Asakura.EndToEnd
open Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The closed derivative and all cylinder-density inputs used in the smooth
 density theorem are constructed from one and the same Wiener system. -/
theorem malliavin_constructed_domain {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [SecondCountableTopology H] [CompleteSpace H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (h : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (h t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (hgen : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤), ∀ f : Lp ℝ q P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) :
    ∃ D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P, D.IsClosed ∧
      (D.graph : Set _) = closure (range (cylinderPair P W S hS hcore 2 (by simp))) ∧
      DenseRange (fun f : D.domain => (f : Lp ℝ 2 P)) ∧
      (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤),
        DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) := by
  have hdense (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤) :=
    concrete_cylinder_dense P W S hS hcore X hXm hXc h hXW times htimes q hq (hgen q hq)
  obtain ⟨D,hclosed,hgraph⟩ := closed_cylinder_graph_from_data P W S hS hcore
    X hXm hXc h hXW times htimes 2 2 (by simp) (by simp) (hgen 2 (by simp))
  refine ⟨D,hclosed,hgraph,?_,hdense⟩
  apply (hdense 2 (by simp)).mono
  rintro _ ⟨c,rfl⟩
  have hc : cylinderPair P W S hS hcore 2 (by simp) c ∈ D.graph := by
    change cylinderPair P W S hS hcore 2 (by simp) c ∈ (D.graph : Set _)
    rw [hgraph]
    exact subset_closure (mem_range_self c)
  obtain ⟨f,hf,_⟩ := D.mem_graph_iff.mp hc
  exact ⟨f,hf⟩

#print axioms malliavin_constructed_domain
end Asakura.EndToEnd
