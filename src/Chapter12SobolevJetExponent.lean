import Chapter12CylinderJetConstruction
import Chapter12VectorCylinderExponent

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Exponent inclusion preserves every actually constructed cylinder derivative. -/
theorem cylinder_jet_coordinate_exponent {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] (hpq : p≤q) (hp : p≠⊤) (hq : q≠⊤)
    (c : SmoothCylinder H) (n : ℕ) :
    probabilityLpInclusion P p q hpq (cylinderJetCoordinate H P W S hS hcore q hq c n)=
      cylinderJetCoordinate H P W S hS hcore p hp c n := by
  cases n with
  | zero =>
    apply Lp.ext
    exact (probabilityLpInclusion_coe P p q hpq (c.valueLp P W S hS hcore q hq)).trans
      ((c.value_memLp P W S hS hcore q hq).coeFn_toLp.trans
        (c.value_memLp P W S hS hcore p hp).coeFn_toLp.symm)
  | succ n => exact vector_cylinder_exponent P W S hS hcore p q hpq hp hq _

/-- Continuous coordinatewise inclusions map the completion of a common
smooth core into the other completion. -/
theorem jet_completion_map {ι : Type*} {n : ℕ} (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)]
    (E F : Fin (n+1) → Type*)
    [∀ j,NormedAddCommGroup (E j)] [∀ j,NormedSpace ℝ (E j)]
    [∀ j,NormedAddCommGroup (F j)] [∀ j,NormedSpace ℝ (F j)]
    (J : ∀ j,E j →L[ℝ] F j) (u : ι → PiLp q E) (v : ι → PiLp p F)
    (huv : ∀ c j,J j (u c j)=v c j) :
    ∃ L : PiLp q E →L[ℝ] PiLp p F,
      (∀ x j,L x j=J j (x j)) ∧
      ∀ x∈(Submodule.span ℝ (range u)).topologicalClosure,
        L x∈(Submodule.span ℝ (range v)).topologicalClosure := by
  let K : PiLp q E →L[ℝ] (∀ j,F j) :=
    ContinuousLinearMap.pi (fun j => (J j).comp (PiLp.proj q E j))
  let L : PiLp q E →L[ℝ] PiLp p F :=
    (PiLp.continuousLinearEquiv p ℝ F).symm.toContinuousLinearMap.comp K
  have hL (x : PiLp q E) (j) : L x j=J j (x j) := rfl
  have hc (c : ι) : L (u c)=v c := by
    apply PiLp.ext
    intro j
    exact huv c j
  refine ⟨L,hL,?_⟩
  let V := (Submodule.span ℝ (range v)).topologicalClosure
  have hs : Submodule.span ℝ (range u)≤V.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c,rfl⟩
    change L (u c)∈V
    rw [hc]
    exact (Submodule.span ℝ (range v)).le_topologicalClosure (Submodule.subset_span (mem_range_self c))
  have hclosed : IsClosed (L ⁻¹' (V : Set _)) :=
    (Submodule.span ℝ (range v)).isClosed_topologicalClosure.preimage L.continuous
  exact closure_minimal hs hclosed

end Asakura.Chapter12
