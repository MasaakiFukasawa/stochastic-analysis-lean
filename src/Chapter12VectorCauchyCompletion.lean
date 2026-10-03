import Chapter12VectorSobolevJetCore

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem vector_cauchy_jet_limit {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (k : ℕ) (c : ℕ → VectorCylinderExpr H H)
    (hc : ∀j : Fin (k+1),CauchySeq (fun n => (iteratedVectorCylinderExpr H (c n) j.val).valueLp P W S hS hcore p hp))
    (f : Lp H p P) (hf : Tendsto (fun n => (c n).valueLp P W S hS hcore p hp) atTop (𝓝 f)) :
    ∃x : vectorSobolevJetSpace H P W S hS hcore p hp k,x.val 0=f := by
  classical
  let E : Fin (k+1) → Type _ := fun j => Lp (positiveMalliavinTensorPower H j.val) p P
  have hex : ∀j : Fin (k+1),∃x : E j,Tendsto (fun n => (iteratedVectorCylinderExpr H (c n) j.val).valueLp P W S hS hcore p hp) atTop (𝓝 x) :=
    fun j => cauchySeq_tendsto_of_complete (hc j)
  choose x hx using hex
  let y : PiLp 1 E := WithLp.toLp 1 x
  have hlim : Tendsto (fun n => WithLp.toLp 1 (fun j : Fin (k+1) => (iteratedVectorCylinderExpr H (c n) j.val).valueLp P W S hS hcore p hp)) atTop (𝓝 y) :=
    ((PiLp.continuous_toLp 1 E).tendsto x).comp (tendsto_pi_nhds.mpr hx)
  have hy : y∈vectorSobolevJetSpace H P W S hS hcore p hp k := by
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    exact Eventually.of_forall (fun n => (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨c n,rfl⟩))
  refine ⟨⟨y,hy⟩,?_⟩
  exact tendsto_nhds_unique (hx 0) hf
end Asakura.Chapter12
#print axioms Asakura.Chapter12.vector_cauchy_jet_limit
