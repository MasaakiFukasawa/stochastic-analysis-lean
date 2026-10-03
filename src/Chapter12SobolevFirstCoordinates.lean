import Chapter12AllSobolevFirstGraph

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_first_coordinates_graph {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤)
    (D : Lp ℝ p P →ₗ.[ℝ] Lp H p P)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore p hp)))
    (k : ℕ) (x : malliavinSobolevJetSpace H P W S hS hcore q hq (k+1)) :
    (probabilityLpInclusion P p q hpq (x.val 0),probabilityLpInclusion P p q hpq (x.val 1))∈D.graph := by
  let E : Fin (k+1+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) q P
  let J : PiLp q E →L[ℝ] Lp ℝ p P × Lp H p P :=
    ((probabilityLpInclusion P p q hpq).comp (PiLp.proj q E 0)).prod
      ((probabilityLpInclusion P p q hpq).comp (PiLp.proj q E 1))
  let jet := fun c : SmoothCylinder H => WithLp.toLp q
    ((fun j:Fin (k+1+1) => cylinderJetCoordinate H P W S hS hcore q hq c j.val) : ∀j,E j)
  have hc (c : SmoothCylinder H) : J (jet c)∈D.graph := by
    change (probabilityLpInclusion P p q hpq (cylinderJetCoordinate H P W S hS hcore q hq c 0),
      probabilityLpInclusion P p q hpq (cylinderJetCoordinate H P W S hS hcore q hq c 1))∈D.graph
    rw [cylinder_jet_coordinate_exponent H P W S hS hcore p q hpq hp hq c 0,
      cylinder_jet_coordinate_exponent H P W S hS hcore p q hpq hp hq c 1]
    change (c.valueLp P W S hS hcore p hp,(cylinderFirstGradientExpr c).valueLp P W S hS hcore p hp)∈D.graph
    rw [scalar_gradient_expression P W S hS hcore p hp c]
    change cylinderPair P W S hS hcore p hp c∈(D.graph : Set _)
    rw [hg]
    exact subset_closure (mem_range_self c)
  have hs : Submodule.span ℝ (range jet)≤D.graph.comap J.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    exact hc c
  have hclosed : IsClosed (J ⁻¹' (D.graph : Set _)) := by
    have hDc : IsClosed (D.graph : Set (Lp ℝ p P × Lp H p P)) := by rw [hg];exact isClosed_closure
    exact hDc.preimage J.continuous
  exact (closure_minimal hs hclosed) x.property
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_first_coordinates_graph
