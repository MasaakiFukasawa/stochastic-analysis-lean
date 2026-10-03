import Chapter12SobolevSpacesFromWienerData
import Chapter12WienerSquareCylinder

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable def malliavinSobolevJetSpace {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (k : ℕ) :
    Submodule ℝ (PiLp p (fun j : Fin (k+1) => Lp (malliavinTensorOrder H j.val) p P)) :=
  (Submodule.span ℝ (range (fun c : SmoothCylinder H => WithLp.toLp p
    ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) :
      ∀ j : Fin (k+1), Lp (malliavinTensorOrder H j.val) p P)))).topologicalClosure

/-- This quantifies over every finite exponent and every derivative order,
using the actual completed jet spaces, not a separate smoothness predicate. -/
def HasAllSobolevJets {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (F : Ω → ℝ) : Prop :=
  ∀ (p : ℝ≥0∞) (hp1 : 1≤p) (hp : p≠⊤) (k : ℕ),
    letI : Fact (1≤p) := ⟨hp1⟩
    ∃ x : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      (x.val 0 : Ω → ℝ)=ᵐ[P] F

theorem cylinder_all_sobolev_orders {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (c : SmoothCylinder H) (F : Ω → ℝ) (hF : c.value P W=ᵐ[P] F) :
    HasAllSobolevJets H P W S hS hcore F := by
  intro p hp1 hp k
  letI : Fact (1≤p) := ⟨hp1⟩
  let x : PiLp p (fun j : Fin (k+1) => Lp (malliavinTensorOrder H j.val) p P) :=
    WithLp.toLp p ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) :
      ∀ j : Fin (k+1), Lp (malliavinTensorOrder H j.val) p P)
  have hx : x∈malliavinSobolevJetSpace H P W S hS hcore p hp k :=
    (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨c,rfl⟩)
  refine ⟨⟨x,hx⟩,?_⟩
  exact (c.value_memLp P W S hS hcore p hp).coeFn_toLp.trans hF

theorem wiener_linear_square_all_orders {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (h : H) (F : Ω → ℝ) (hF : (W h : Ω → ℝ)=ᵐ[P] F) :
    HasAllSobolevJets H P W S hS hcore F ∧
    HasAllSobolevJets H P W S hS hcore (fun w => F w^2) := by
  constructor
  · apply cylinder_all_sobolev_orders H P W S hS hcore (linearSmoothCylinder h)
    simpa only [linear_cylinder_value] using hF
  · apply cylinder_all_sobolev_orders H P W S hS hcore (squareWienerCylinder h)
    rw [square_wiener_cylinder_value]
    exact hF.mono (fun w hw => congrArg (fun z : ℝ => z^2) hw)

end Asakura.Chapter12
