import Chapter12ConcreteCylinderOperator

open MeasureTheory ProbabilityTheory Set ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem cylinder_value_equality_all_exponents {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h∈S,HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (c d : SmoothCylinder H) (p q : ℝ≥0∞) (hp : p≠⊤) (hq : q≠⊤)
    (he : c.valueLp P W S hS hcore p hp=d.valueLp P W S hS hcore p hp) :
    c.valueLp P W S hS hcore q hq=d.valueLp P W S hS hcore q hq := by
  have hc := (c.value_memLp P W S hS hcore p hp).coeFn_toLp
  have hd := (d.value_memLp P W S hS hcore p hp).coeFn_toLp
  change (c.valueLp P W S hS hcore p hp : Ω → ℝ)=ᵐ[P] c.value P W at hc
  rw [he] at hc
  have hraw := hc.symm.trans hd
  apply Lp.ext
  exact ((c.value_memLp P W S hS hcore q hq).coeFn_toLp.trans hraw).trans
    (d.value_memLp P W S hS hcore q hq).coeFn_toLp.symm

end Asakura.Chapter12
