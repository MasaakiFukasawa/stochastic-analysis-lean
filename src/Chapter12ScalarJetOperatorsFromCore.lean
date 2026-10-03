import Chapter12CylinderJetConstruction
import Chapter12VectorHigherCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

/-- All scalar derivative graphs are constructed from the Wiener core. -/
theorem scalar_jet_operators_from_core {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq)) :
    ∃ D : ∀ n,Lp (malliavinTensorOrder H n) p P →ₗ.[ℝ]
      Lp (malliavinTensorOrder H (n+1)) p P,
      (∀ n,(D n).IsClosed) ∧ ∀ c n,
      (cylinderJetCoordinate H P W S hS hcore p hp c n,
       cylinderJetCoordinate H P W S hS hcore p hp c (n+1))∈(D n).graph := by
  obtain ⟨A,hgraph,hclos,hfirst⟩ := concrete_cylinder_operator P W S hS hcore p q hp hq hdense
  apply cylinder_jet_closed_operators H P W S hS hcore p q hp hq hdense A.closure hclos.closure_isClosed
  intro c
  rw [← hclos.graph_closure_eq_closure_graph]
  exact A.graph.le_topologicalClosure (hfirst c)

/-- Equality in scalar Lp determines every higher derivative on the
actual core. -/
theorem scalar_jet_core_unique {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (c d : SmoothCylinder H)
    (h0 : c.valueLp P W S hS hcore p hp=d.valueLp P W S hS hcore p hp) :
    ∀ k,cylinderJetCoordinate H P W S hS hcore p hp c k=
      cylinderJetCoordinate H P W S hS hcore p hp d k := by
  obtain ⟨D,hclosed,hD⟩ := scalar_jet_operators_from_core H P W S hS hcore p q hp hq hdense
  exact closed_jet_all_orders_unique _ D _ _ (hD c) (hD d) h0

end Asakura.Chapter12
