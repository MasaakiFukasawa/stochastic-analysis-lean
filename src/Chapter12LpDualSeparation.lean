import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory Set Filter ENNReal
open scoped Topology
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Dense Lq test functions separate scalar Lp random variables. The last step
uses indicators of measurable sets, so no unproved Lp duality identification
is required. -/
theorem scalar_Lp_separated_by_dense_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (S : Set (Lp ℝ q P)) (hS : Dense S) (u : Lp ℝ p P)
    (hu : ∀ v ∈ S, ∫ w, u w*v w ∂P = 0) : u = 0 := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  let L := B.lpPairing P p q u
  have hL : ∀ v, L v = 0 := by
    apply isClosed_property hS.denseRange_val
      (isClosed_eq L.continuous continuous_const)
    intro v
    simpa only [L,B,ContinuousLinearMap.lpPairing_eq_integral,ContinuousLinearMap.mul_apply'] using hu v.val v.property
  have hz : (u : Ω → ℝ) =ᵐ[P] 0 := by
    apply ((Lp.memLp u).integrable (Fact.out : 1 ≤ p)).ae_eq_zero_of_forall_setIntegral_eq_zero
    intro s hs _
    have hi : MemLp (s.indicator (fun _ : Ω => (1 : ℝ))) q P := (memLp_const 1).indicator hs
    have he := hL (hi.toLp _)
    rw [show L (hi.toLp _) = ∫ w, u w*(hi.toLp _ : Ω → ℝ) w ∂P from
      ContinuousLinearMap.lpPairing_eq_integral B u (hi.toLp _)] at he
    have hei : (fun w => u w*(hi.toLp _ : Ω → ℝ) w) =ᵐ[P] s.indicator (u : Ω → ℝ) := by
      filter_upwards [hi.coeFn_toLp] with w hw
      rw [hw]
      by_cases hws : w ∈ s <;> simp [Set.indicator,hws]
    rw [integral_congr_ae hei,integral_indicator hs] at he
    exact he
  exact Lp.ext (hz.trans (Lp.coeFn_zero ℝ p P).symm)

/-- The Hilbert-valued conclusion follows from scalar pairings in a countable
dense family of directions, as in the manuscript. -/
theorem hilbert_Lp_separated_by_dense_tests {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SecondCountableTopology H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [HolderConjugate p q]
    (S : Set (Lp ℝ q P)) (hS : Dense S) (u : Lp H p P)
    (hu : ∀ h : H, ∀ v ∈ S, ∫ w, (inner ℝ h (u w))*v w ∂P = 0) : u = 0 := by
  have hz : (u : Ω → H) =ᵐ[P] 0 := by
    apply ae_eq_zero_of_forall_inner (𝕜 := ℝ)
    intro h
    let A := innerSL ℝ h
    let z := A.compLp u
    have hz0 : z = 0 := scalar_Lp_separated_by_dense_tests P p q S hS z (by
      intro v hv
      rw [integral_congr_ae (show (fun w => z w*v w) =ᵐ[P]
        (fun w => (inner ℝ h (u w))*v w) from by
          filter_upwards [A.coeFn_compLp u] with w hw
          rw [hw]; rfl)]
      exact hu h v hv)
    have hae : (z : Ω → ℝ) =ᵐ[P] (fun w => inner ℝ h (u w)) := A.coeFn_compLp u
    have he0 : (z : Ω → ℝ) =ᵐ[P] 0 := by
      rw [hz0]
      exact Lp.coeFn_zero ℝ p P
    exact hae.symm.trans he0
  exact Lp.ext (hz.trans (Lp.coeFn_zero H p P).symm)

end Asakura.Chapter12
