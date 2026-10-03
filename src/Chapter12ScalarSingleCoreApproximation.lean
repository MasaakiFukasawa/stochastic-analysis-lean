import Chapter12ScalarSobolevSumJet
import Chapter12CylinderAllSobolevOrders

open MeasureTheory ProbabilityTheory Set ENNReal Filter
open scoped Topology
namespace Asakura.Chapter12
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem scalar_single_core_approximation {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1≤p)] [Fact (1≤q)] [HolderConjugate p q]
    (hp : p≠⊤) (hq : q≠⊤)
    (hdense : DenseRange (fun c : SmoothCylinder H => c.valueLp P W S hS hcore q hq))
    (k : ℕ) (x : malliavinSobolevJetSpace H P W S hS hcore p hp k) :
    ∃c : ℕ → SmoothCylinder H,
      Tendsto (fun n => scalarSobolevSumCoreJet H P W S hS hcore p hp k (c n)) atTop
        (𝓝 (WithLp.toLp 1 (fun j => x.val j))) := by
  obtain ⟨D,hD,hcoreD⟩ := scalar_jet_operators_from_core H P W S hS hcore p q hp hq hdense
  let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  let jet : SmoothCylinder H → PiLp p E := fun c => WithLp.toLp p
    ((fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp c j.val) : ∀j,E j)
  let A : ∀j:Fin k,E j.castSucc →ₗ.[ℝ] E j.succ := fun j => D j.val
  have hspan := cylinder_jet_span_range P W S hS hcore p hp E A jet
    (fun c j => hcoreD c j.val) (LinearMap.id : Lp ℝ p P →ₗ[ℝ] E 0) (fun _ => rfl)
  obtain ⟨c,hc⟩ := jet_single_core_approximation p E jet hspan x
  refine ⟨c,?_⟩
  have hcoords := (PiLp.continuous_ofLp p E).tendsto x.val |>.comp hc
  exact ((PiLp.continuous_toLp 1 E).tendsto (fun j => x.val j)).comp hcoords
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_single_core_approximation
