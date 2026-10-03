import Chapter6L2WeightedRegression
import Chapter9ConditionalFubini
import Chapter10InnovationErrorConditional

open MeasureTheory Set
open scoped BigOperators
namespace Asakura.Chapter10
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- In the innovation product formula the current innovation is measurable
in current information. Multiplication by it preserves the zero conditional
mean of the error; C5 then permits conditioning at an earlier time. -/
theorem conditional_linear_error_product_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (G H : MeasurableSpace Ω) (hGH : G≤H) (hH : H≤m)
    (e : Fin d → Ω → ℝ) (Y : Ω → ℝ) (c : Fin d → ℝ)
    (he : ∀ i,MemLp (e i) 2 P) (hY : MemLp Y 2 P) (hYm : Measurable[H] Y)
    (hz : ∀ i,P[e i|H]=ᵐ[P] (fun _ => (0:ℝ))) :
    P[(fun w => Y w*(∑ i,c i*e i w))|G]=ᵐ[P] (fun _ => (0:ℝ)) := by
  have hi i : Integrable (fun w => c i*(Y w*e i w)) P :=
    (hY.integrable_mul (he i)).const_mul _
  have hc i : P[(fun w => c i*(Y w*e i w))|G]=ᵐ[P] (fun _ => (0:ℝ)) := by
    have hh := Asakura.Chapter6.L2_weighted_conditional_regression P (e i) (fun _ => 0) Y
      (he i) (memLp_const 0) hY G H hGH hH hYm (hz i)
    have hh' : P[(fun w => Y w*e i w)|G]=ᵐ[P] (fun _ => (0:ℝ)) := by
      simpa only [mul_zero,←Pi.zero_def,condExp_zero] using hh
    filter_upwards [condExp_smul (c i) (fun w => Y w*e i w) G,hh'] with w hw hz'
    simpa only [Pi.smul_apply,smul_eq_mul,hz',mul_zero] using! hw
  have hs := condExp_finsetSum (s := Finset.univ) (fun i _ => hi i) (m := G)
  have heq : (fun w => Y w*(∑ i,c i*e i w))=(fun w => ∑ i,c i*(Y w*e i w)) := by
    funext w
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  have hf : (∑ i : Fin d,fun w => c i*(Y w*e i w))=(fun w => ∑ i,c i*(Y w*e i w)) := by
    funext w
    simp only [Finset.sum_apply]
  rw [hf] at hs
  filter_upwards [hs,ae_all_iff.mpr hc] with w hw hc'
  simpa only [Finset.sum_apply,hc',Finset.sum_const_zero] using! hw

end Asakura.Chapter10
