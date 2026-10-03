import Chapter12ConcreteCylinderDensity

open MeasureTheory ProbabilityTheory Set Filter ENNReal
open scoped Topology RealInnerProductSpace
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Concrete construction and closed extension of the Malliavin--Shigekawa
operator. Density and Gaussian IBP are derived from the stated Wiener data,
not supplied as assumptions about an already defined derivative. -/
theorem closed_malliavin_operator_from_wiener_data
    {Ω H K : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    [SecondCountableTopology H] [CompleteSpace H]
    [TopologicalSpace K] [FirstCountableTopology K]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ)
      (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (direction : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (direction t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hgen : ∀ f : Lp ℝ q P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) :
    ∃ D : Lp ℝ p P →ₗ.[ℝ] Lp H p P,
      D.IsClosable ∧ D.closure.IsClosed ∧ CompleteSpace D.closure.graph ∧
      (∀ c : SmoothCylinder H,
        (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp) ∈ D.graph) ∧
      D.closure.graph = (Submodule.span ℝ (range (fun c : SmoothCylinder H =>
        (c.valueLp P W S hS hcore p hp,c.gradientLp P W S hS hcore p hp)))).topologicalClosure := by
  have hd := concrete_cylinder_dense P W S hS hcore X hXm hXc direction hXW
    times htimes q hq hgen
  obtain ⟨D,hgraph,hD,hcyl⟩ := concrete_cylinder_operator P W S hS hcore p q hp hq hd
  refine ⟨D,hD,hD.closure_isClosed,derivative_graph_complete D hD,hcyl,?_⟩
  rw [← hD.graph_closure_eq_closure_graph,hgraph]

end Asakura.Chapter12
