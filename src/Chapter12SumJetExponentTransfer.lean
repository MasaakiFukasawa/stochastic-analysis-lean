import Chapter12ScalarSobolevSumJet
import Chapter12CylinderAllSobolevOrders
import Chapter12HigherSobolevCompatibility

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- The sum norm used for the estimates and the existing Sobolev jet
norm give the same completion; decreasing the exponent preserves all
actual derivative coordinates. -/
theorem scalar_sum_jet_exponent_transfer {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤)
    (k : ℕ)
    (y : (Submodule.span ℝ (range (scalarSobolevSumCoreJet H P W S hS hcore q hq k))).topologicalClosure) :
    ∃ x : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      (x.val 0 : Ω → ℝ)=ᵐ[P] (y.val 0 : Ω → ℝ) := by
  let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) q P
  let F : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  let v := fun c : SmoothCylinder H => WithLp.toLp p
    ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀ j,F j)
  let u : SmoothCylinder H → PiLp 1 E := scalarSobolevSumCoreJet H P W S hS hcore q hq k
  let J : ∀ j,E j →L[ℝ] F j := fun j => probabilityLpInclusion (E:=malliavinTensorOrder H j.val) P p q hpq
  have huv : ∀ c j,J j (u c j)=v c j := by
    intro c j
    exact cylinder_jet_coordinate_exponent H P W S hS hcore p q hpq hp hq c j.val
  obtain ⟨L,hL,hmap⟩ := jet_completion_map p 1 E F J u v huv
  refine ⟨⟨L y.val,hmap y.val y.property⟩,?_⟩
  change (L y.val 0 : Ω → ℝ)=ᵐ[P] (y.val 0 : Ω → ℝ)
  rw [hL]
  exact probabilityLpInclusion_coe P p q hpq (y.val 0)

end Asakura.Chapter12
