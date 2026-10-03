import Chapter12ConstructedSobolevSpaces
import Chapter12ClosedMalliavinOperator

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The completed Sobolev space of any finite order, built from actual
iterated smooth cylinders, is complete and embeds injectively into scalar Lp.
The derivative coordinates satisfy the closed derivative equations. -/
theorem sobolev_spaces_from_wiener_data {Ω K : Type*} [MeasurableSpace Ω]
    [TopologicalSpace K] [FirstCountableTopology K]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (X : K → Ω → ℝ) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ w, Continuous (fun t => X t w))
    (direction : K → H) (hXW : ∀ t, X t =ᵐ[P] (W (direction t) : Ω → ℝ))
    (times : ℕ → K) (htimes : DenseRange times)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hgen : ∀ f : Lp ℝ q P,
      AEStronglyMeasurable[MeasurableSpace.comap (fun w t => X t w) inferInstance] f P) (k : ℕ) :
    let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
    let jet := fun c : SmoothCylinder H =>
      WithLp.toLp p ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀ j : Fin (k+1), Lp (malliavinTensorOrder H j.val) p P)
    let G := (Submodule.span ℝ (range jet)).topologicalClosure
    CompleteSpace G ∧ Function.Injective (fun x : G => x.val 0) ∧
      ∀ x : G,∃ c : ℕ → SmoothCylinder H,
        Filter.Tendsto (fun m => jet (c m)) Filter.atTop (𝓝 x.val) := by
  have hdense := concrete_cylinder_dense P W S hS hcore X hXm hXc direction hXW times htimes q hq hgen
  obtain ⟨D,hclos,hclosed,_,hfirst,_⟩ := closed_malliavin_operator_from_wiener_data
    P W S hS hcore X hXm hXc direction hXW times htimes p q hp hq hgen
  have hc : ∀ c : SmoothCylinder H,(c.valueLp P W S hS hcore p hp,
      c.gradientLp P W S hS hcore p hp)∈D.closure.graph := by
    intro c
    rw [←hclos.graph_closure_eq_closure_graph]
    exact D.graph.le_topologicalClosure (hfirst c)
  exact constructed_sobolev_spaces H P W S hS hcore p q hp hq hdense D.closure hclosed hc k

end Asakura.Chapter12
