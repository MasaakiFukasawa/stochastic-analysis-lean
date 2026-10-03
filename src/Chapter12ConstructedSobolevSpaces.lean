import Chapter12CylinderJetConstruction
import Chapter12CylinderJetApproximation

open MeasureTheory ProbabilityTheory Set ENNReal TopologicalSpace
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The completed Sobolev space of any finite order, built from actual
iterated smooth cylinders, is complete and embeds injectively into scalar Lp.
The derivative coordinates satisfy the closed derivative equations. -/
theorem constructed_sobolev_spaces {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (D₀ : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (hclosed : D₀.IsClosed)
    (hfirst : ∀ c : SmoothCylinder H,(c.valueLp P W S hS hcore p hp,
      c.gradientLp P W S hS hcore p hp)∈D₀.graph) (k : ℕ) :
    let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
    let jet := fun c : SmoothCylinder H =>
      WithLp.toLp p ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀ j : Fin (k+1), Lp (malliavinTensorOrder H j.val) p P)
    let G := (Submodule.span ℝ (range jet)).topologicalClosure
    CompleteSpace G ∧ Function.Injective (fun x : G => x.val 0) ∧
      ∀ x : G,∃ c : ℕ → SmoothCylinder H,
        Filter.Tendsto (fun m => jet (c m)) Filter.atTop (𝓝 x.val) := by
  obtain ⟨D,hD,hjet⟩ := cylinder_jet_closed_operators H P W S hS hcore p q hp hq hdense D₀ hclosed hfirst
  let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  let jet : SmoothCylinder H → PiLp p E := fun c =>
    WithLp.toLp p ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀ j : Fin (k+1), Lp (malliavinTensorOrder H j.val) p P)
  let A : ∀ j : Fin k,E j.castSucc →ₗ.[ℝ] E j.succ := fun j => D j.val
  have hA : ∀ j : Fin k,(A j).IsClosed := fun j => hD j.val
  have hc : ∀ c j,(jet c j.castSucc,jet c j.succ)∈(A j).graph := fun c j => hjet c j.val
  obtain ⟨hcomplete,hinj,_⟩ := sobolev_jet_completion p E A hA jet hc
  have hspan := cylinder_jet_span_range P W S hS hcore p hp E A jet hc
    (LinearMap.id : Lp ℝ p P →ₗ[ℝ] E 0) (fun c => rfl)
  exact ⟨hcomplete,hinj,fun x => jet_single_core_approximation p E jet hspan x⟩

end Asakura.Chapter12
