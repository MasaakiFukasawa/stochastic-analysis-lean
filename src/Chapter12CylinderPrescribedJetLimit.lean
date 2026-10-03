import Chapter12CylinderCauchyCompletion

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem cylinder_prescribed_jet_limit {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤) (k : ℕ) (c : ℕ → SmoothCylinder H)
    (x : ∀j:Fin (k+1),Lp (malliavinTensorOrder H j.val) p P)
    (hx : ∀j:Fin (k+1),Tendsto (fun n => cylinderJetCoordinate H P W S hS hcore p hp (c n) j.val)
      atTop (𝓝 (x j))) :
    ∃J : malliavinSobolevJetSpace H P W S hS hcore p hp k,∀j,J.val j=x j := by
  let E := fun j:Fin (k+1) => (Lp (malliavinTensorOrder H j.val) p P : Type _)
  have hlim : Tendsto (fun n => WithLp.toLp p (fun j:Fin (k+1) => cylinderJetCoordinate H P W S hS hcore p hp (c n) j.val))
      atTop (𝓝 (WithLp.toLp p x)) :=
    ((PiLp.continuous_toLp p E).tendsto x).comp (tendsto_pi_nhds.mpr hx)
  have hmem : WithLp.toLp p x∈malliavinSobolevJetSpace H P W S hS hcore p hp k := by
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
    exact Eventually.of_forall (fun n => (Submodule.span ℝ _).le_topologicalClosure (Submodule.subset_span ⟨c n,rfl⟩))
  exact ⟨⟨WithLp.toLp p x,hmem⟩,fun _ => rfl⟩
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_prescribed_jet_limit
