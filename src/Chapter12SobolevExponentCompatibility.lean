import Chapter12LpInclusion
import Chapter12CylinderPairLinear

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

/-- The closed Malliavin derivative is compatible with decreasing the Lp
exponent. Thus the intersection defining D-infinity uses one derivative,
not different incompatible closed extensions. -/
theorem closed_malliavin_exponent_compatibility {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : H →ₗᵢ[ℝ] Lp ℝ 2 P) (S : Set H) (hS : Dense S)
    (hcore : ∀ h ∈ S, HasLaw (W h : Ω → ℝ) (gaussianReal 0 ⟨‖h‖^2,sq_nonneg _⟩) P)
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (Dp : Lp ℝ p P →ₗ.[ℝ] Lp H p P) (Dq : Lp ℝ q P →ₗ.[ℝ] Lp H q P)
    (hgp : (Dp.graph : Set _) = closure (range (cylinderPair P W S hS hcore p hp)))
    (hgq : (Dq.graph : Set _) = closure (range (cylinderPair P W S hS hcore q hq)))
    (F : Lp ℝ q P) (U : Lp H q P) (hFU : (F,U) ∈ Dq.graph) :
    (probabilityLpInclusion P p q hpq F,probabilityLpInclusion P p q hpq U) ∈ Dp.graph := by
  let J := fun z : Lp ℝ q P × Lp H q P =>
    (probabilityLpInclusion P p q hpq z.1,probabilityLpInclusion P p q hpq z.2)
  have hJ : Continuous J := by unfold J; fun_prop
  have he (c : SmoothCylinder H) : J (cylinderPair P W S hS hcore q hq c) =
      cylinderPair P W S hS hcore p hp c := by
    apply Prod.ext
    · apply Lp.ext
      exact (probabilityLpInclusion_coe P p q hpq (c.valueLp P W S hS hcore q hq)).trans
        ((c.value_memLp P W S hS hcore q hq).coeFn_toLp.trans
          (c.value_memLp P W S hS hcore p hp).coeFn_toLp.symm)
    · apply Lp.ext
      exact (probabilityLpInclusion_coe P p q hpq (c.gradientLp P W S hS hcore q hq)).trans
        ((c.gradient_memLp P W S hS hcore q hq).coeFn_toLp.trans
          (c.gradient_memLp P W S hS hcore p hp).coeFn_toLp.symm)
  have hclosed : IsClosed (Dp.graph : Set (Lp ℝ p P × Lp H p P)) := by
    rw [hgp]
    exact isClosed_closure
  have hs : closure (range (cylinderPair P W S hS hcore q hq)) ⊆ J ⁻¹' (Dp.graph : Set _) := by
    apply closure_minimal
    · rintro _ ⟨c,rfl⟩
      change J (cylinderPair P W S hS hcore q hq c) ∈ (Dp.graph : Set _)
      rw [he,hgp]
      exact subset_closure (mem_range_self c)
    · exact hclosed.preimage hJ
  have hz : (F,U) ∈ closure (range (cylinderPair P W S hS hcore q hq)) := by
    rw [← hgq]
    exact hFU
  exact hs hz

end Asakura.Chapter12
