import Chapter12CylinderAllSobolevOrders

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

theorem cylinder_value_equality {Ω : Type*} [MeasurableSpace Ω]
    (H : RealHilbertSpaceData) [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p : ℝ≥0∞) [Fact (1≤p)] (hp : p≠⊤)
    (c d : SmoothCylinder H) (hc : c.value P W=ᵐ[P] d.value P W) :
    c.valueLp P W S hS hcore p hp=d.valueLp P W S hS hcore p hp := by
  apply Lp.ext
  exact (c.value_memLp P W S hS hcore p hp).coeFn_toLp.trans
    (hc.trans (d.value_memLp P W S hS hcore p hp).coeFn_toLp.symm)
end Asakura.Chapter12
#print axioms Asakura.Chapter12.cylinder_value_equality
