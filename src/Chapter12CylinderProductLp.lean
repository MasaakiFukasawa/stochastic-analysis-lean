import Chapter12CylinderProduct
import Chapter12CylinderPairLinear
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem cylinder_product_Lp_pair {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderTriple q q p]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (c d : SmoothCylinder H) :
    cylinderPair P W S hS hcore p hp (mulSmoothCylinder c d) =
    ((ContinuousLinearMap.mul ℝ ℝ).holderL P q q p (c.valueLp P W S hS hcore q hq) (d.valueLp P W S hS hcore q hq),
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p
        (d.valueLp P W S hS hcore q hq) (c.gradientLp P W S hS hcore q hq)+
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p
        (c.valueLp P W S hS hcore q hq) (d.gradientLp P W S hS hcore q hq)) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [((mulSmoothCylinder c d).value_memLp P W S hS hcore p hp).coeFn_toLp,
      (c.value_memLp P W S hS hcore q hq).coeFn_toLp,
      (d.value_memLp P W S hS hcore q hq).coeFn_toLp,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := p)
        (c.valueLp P W S hS hcore q hq) (d.valueLp P W S hS hcore q hq)] with w h1 h2 h3 h4
    dsimp only [cylinderPair,SmoothCylinder.valueLp] at *
    simp only [ContinuousLinearMap.holderL_apply_apply,ContinuousLinearMap.holderₗ_apply_apply]
    rw [h1,h4,h2,h3,mulSmoothCylinder_value]
    rfl
  · let B := (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).holderL P q q p
    let A := B (d.valueLp P W S hS hcore q hq) (c.gradientLp P W S hS hcore q hq)
    let C := B (c.valueLp P W S hS hcore q hq) (d.gradientLp P W S hS hcore q hq)
    apply Lp.ext
    filter_upwards [((mulSmoothCylinder c d).gradient_memLp P W S hS hcore p hp).coeFn_toLp,
      (c.value_memLp P W S hS hcore q hq).coeFn_toLp,
      (d.value_memLp P W S hS hcore q hq).coeFn_toLp,
      (c.gradient_memLp P W S hS hcore q hq).coeFn_toLp,
      (d.gradient_memLp P W S hS hcore q hq).coeFn_toLp,
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).coeFn_holder (r := p)
        (d.valueLp P W S hS hcore q hq) (c.gradientLp P W S hS hcore q hq),
      (ContinuousLinearMap.lsmul ℝ ℝ (E := H)).coeFn_holder (r := p)
        (c.valueLp P W S hS hcore q hq) (d.gradientLp P W S hS hcore q hq),
      Lp.coeFn_add A C] with w h1 h2 h3 h4 h5 h6 h7 h8
    change _ = (A+C) w
    rw [h8,Pi.add_apply]
    dsimp only [A,C,B,ContinuousLinearMap.holderL_apply_apply,SmoothCylinder.valueLp,
      SmoothCylinder.gradientLp,cylinderPair] at *
    simp only [ContinuousLinearMap.holderL_apply_apply,ContinuousLinearMap.holderₗ_apply_apply]
    rw [h1,h6,h7,h2,h3,h4,h5,mulSmoothCylinder_gradient]
    rfl

end Asakura.Chapter12
