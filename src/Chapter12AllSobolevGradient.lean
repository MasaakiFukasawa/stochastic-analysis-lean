import Chapter12SobolevDerivativeTail
import Chapter12SobolevFirstCoordinates

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

theorem all_sobolev_gradient {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀u∈S,HasLaw (W u : Ω → ℝ) (gaussianReal 0 ⟨‖u‖^2,sq_nonneg _⟩) P)
    (D : Lp ℝ 2 P →ₗ.[ℝ] Lp H 2 P)
    (hg : (D.graph : Set _)=closure (range (cylinderPair P W S hS hcore 2 (by simp))))
    (F : Lp ℝ 2 P) (U : Lp H 2 P) (hF : HasAllSobolevJets H P W S hS hcore F)
    (hDU : (F,U)∈D.graph) : HasAllVectorSobolevJets H P W S hS hcore U := by
  intro p hp1 hp k
  letI : Fact (1≤p) := ⟨hp1⟩
  obtain ⟨n,hn,hpn,h2n⟩ := even_exponent_dominates p hp
  letI : Fact (1≤((2*n:ℕ):ℝ≥0∞)) := ⟨by exact_mod_cast (show 1≤2*n by omega)⟩
  obtain ⟨x,hx⟩ := hF (2*n:ℕ) Fact.out (ENNReal.natCast_ne_top _) (k+1)
  have hx0 : probabilityLpInclusion P 2 (2*n:ℕ) h2n (x.val 0)=F := by
    apply Lp.ext
    exact (probabilityLpInclusion_coe P 2 (2*n:ℕ) h2n (x.val 0)).trans hx
  have hxD := sobolev_first_coordinates_graph H P W S hS hcore 2 (2*n:ℕ) h2n
    (by simp) (ENNReal.natCast_ne_top _) D hg k x
  rw [hx0] at hxD
  have hx1 := partial_linear_graph_output_unique D hxD hDU
  have hraw : (x.val 1 : Ω → H)=ᵐ[P] (U : Ω → H) := by
    have hh := probabilityLpInclusion_coe P 2 (2*n:ℕ) h2n (x.val 1)
    rw [hx1] at hh
    exact hh.symm
  obtain ⟨y,hy⟩ := sobolev_derivative_tail H P W S hS hcore p (2*n:ℕ) hpn hp
    (ENNReal.natCast_ne_top _) k x
  refine ⟨y,?_⟩
  rw [hy 0]
  exact (probabilityLpInclusion_coe P p (2*n:ℕ) hpn (x.val 1)).trans hraw
end Asakura.Chapter12
#print axioms Asakura.Chapter12.all_sobolev_gradient
