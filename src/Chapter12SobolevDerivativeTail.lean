import Chapter12DivergenceAllSobolev
import Chapter12GaussianScalarHigherCore

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

theorem sobolev_derivative_tail {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤)
    (k : ℕ) (x : malliavinSobolevJetSpace H P W S hS hcore q hq (k+1)) :
    ∃y : vectorSobolevJetSpace H P W S hS hcore p hp k,
      ∀j:Fin (k+1),y.val j=probabilityLpInclusion P p q hpq (x.val j.succ) := by
  let E : Fin (k+1+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) q P
  let F : Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) p P
  let L : PiLp q E →L[ℝ] PiLp 1 F :=
    (PiLp.continuousLinearEquiv 1 ℝ F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun j:Fin (k+1) =>
        (probabilityLpInclusion P p q hpq).comp (PiLp.proj q E j.succ)))
  let jet := fun c : SmoothCylinder H => WithLp.toLp q
    ((fun j:Fin (k+1+1) => cylinderJetCoordinate H P W S hS hcore q hq c j.val) : ∀j,E j)
  have hc (c : SmoothCylinder H) : L (jet c)=
      vectorSobolevCoreJet H P W S hS hcore p hp k (cylinderFirstGradientExpr c) := by
    apply PiLp.ext
    intro j
    change probabilityLpInclusion P p q hpq (cylinderJetCoordinate H P W S hS hcore q hq c (j.val+1))=
      (iteratedVectorCylinderExpr H (cylinderFirstGradientExpr c) j.val).valueLp P W S hS hcore p hp
    rw [cylinder_jet_coordinate_exponent,first_gradient_iterated_expression]
    rfl
  let V := vectorSobolevJetSpace H P W S hS hcore p hp k
  have hs : Submodule.span ℝ (range jet)≤V.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    change L (jet c)∈V
    rw [hc]
    exact (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span (mem_range_self _))
  have hclosed : IsClosed (L ⁻¹' (V : Set _)) :=
    (Submodule.span ℝ _).isClosed_topologicalClosure.preimage L.continuous
  have hx : L x.val∈V := (closure_minimal hs hclosed) x.property
  exact ⟨⟨L x.val,hx⟩,fun _ => rfl⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.sobolev_derivative_tail
