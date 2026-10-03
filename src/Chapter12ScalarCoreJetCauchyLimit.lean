import Chapter12CylinderAllSobolevOrders
import Chapter12ScalarSobolevSumJet

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem scalar_core_jet_cauchy_limit {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (k : ℕ) (c : ℕ → SmoothCylinder H)
    (hc : ∀j : Fin (k+1),CauchySeq (fun n => cylinderJetCoordinate H P W S hS hcore p hp (c n) j.val))
    : ∃x : malliavinSobolevJetSpace H P W S hS hcore p hp k,
      Tendsto (fun n => scalarSobolevSumCoreJet H P W S hS hcore p hp k (c n)) atTop
        (𝓝 (WithLp.toLp 1 (fun j => x.val j))) := by
  classical
  let E : Fin (k+1) → Type _ := fun j => Lp (malliavinTensorOrder H j.val) p P
  have hex : ∀j : Fin (k+1),∃x : E j,Tendsto (fun n => cylinderJetCoordinate H P W S hS hcore p hp (c n) j.val) atTop (𝓝 x) :=
    fun j => cauchySeq_tendsto_of_complete (hc j)
  choose x hx using hex
  let y : PiLp p E := WithLp.toLp p x
  have hlim : Tendsto (fun n => WithLp.toLp p (fun j : Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp (c n) j.val)) atTop (𝓝 y) :=
    ((PiLp.continuous_toLp p E).tendsto x).comp (tendsto_pi_nhds.mpr hx)
  have hy : y∈malliavinSobolevJetSpace H P W S hS hcore p hp k := by
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    exact Eventually.of_forall (fun n => (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨c n,rfl⟩))
  refine ⟨⟨y,hy⟩,?_⟩
  exact ((PiLp.continuous_toLp 1 E).tendsto x).comp (tendsto_pi_nhds.mpr hx)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.scalar_core_jet_cauchy_limit
