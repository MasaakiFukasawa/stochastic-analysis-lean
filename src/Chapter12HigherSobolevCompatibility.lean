import Chapter12SobolevJetExponent

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The actual higher Sobolev completions at different exponents describe
the same random variables and the same derivatives at every order. -/
theorem higher_sobolev_exponent_compatibility {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤) (k : ℕ) :
    let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) q P
    let F : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
    let u : SmoothCylinder H → PiLp q E := fun c => WithLp.toLp q
      ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore q hq c j.val) : ∀ j,E j)
    let v : SmoothCylinder H → PiLp p F := fun c => WithLp.toLp p
      ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀ j,F j)
    ∃ L : PiLp q E →L[ℝ] PiLp p F,
      (∀ x j,L x j=probabilityLpInclusion P p q hpq (x j)) ∧
      ∀ x∈(Submodule.span ℝ (range u)).topologicalClosure,
        L x∈(Submodule.span ℝ (range v)).topologicalClosure := by
  dsimp only
  apply jet_completion_map p q
    (fun j : Fin (k+1) => (Lp (malliavinTensorOrder H j.val) q P : Type _))
    (fun j : Fin (k+1) => (Lp (malliavinTensorOrder H j.val) p P : Type _))
    (fun _ => probabilityLpInclusion P p q hpq)
  intro c j
  exact cylinder_jet_coordinate_exponent H P W S hS hcore p q hpq hp hq c j.val

end Asakura.Chapter12
