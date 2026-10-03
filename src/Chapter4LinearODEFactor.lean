import Chapter4ExponentialWeight

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 1400000

/-- The variational equation in the flow example has an everywhere
positive solution; its exponential representation is derived by an
integrating factor rather than assumed. -/
theorem linear_ode_exponential (a q : ℝ → ℝ) (ha : Continuous a)
    (hq : ∀ x,HasDerivAt q (a x*q x) x) (h0 : q 0=1) :
    ∀ x,q x=Real.exp (∫ r in 0..x,a r) := by
  let A := fun x => ∫ r in 0..x,a r
  have hA x : HasDerivAt A (a x) x :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 x) ha.stronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  let B := fun x => Real.exp (-A x)*q x
  have hB x : HasDerivAt B 0 x := by
    convert ((hA x).neg.exp).mul (hq x) using 1 <;> ring
  have he := is_const_of_deriv_eq_zero (fun x => (hB x).differentiableAt) (fun x => (hB x).deriv)
  intro x
  have hx := he x 0
  have hinit : B 0=1 := by simp [B,A,h0]
  rw [hinit] at hx
  have hh := congrArg (fun y : ℝ => Real.exp (A x)*y) hx
  dsimp only [B] at hh
  rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,mul_one] at hh
  exact hh

end Asakura.Chapter4
