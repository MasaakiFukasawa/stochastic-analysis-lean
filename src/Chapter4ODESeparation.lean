import Chapter4LinearODEFactor

open MeasureTheory Set Filter
open scoped Topology
namespace Asakura.Chapter4
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Under the nonvanishing condition implicit in separation of variables,
the integral of 1/f is an inverse coordinate for the ODE solution. -/
theorem ode_separation_nonvanishing (φ f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ x,f x≠0) (hφ : ∀ x,HasDerivAt φ (f (φ x)) x) (y : ℝ) (h0 : φ 0=y) :
    ∀ x, (∫ u in y..φ x,1/f u)=x := by
  let g := fun u => 1/f u
  have hg : Continuous g := continuous_const.div hf hn
  let A := fun z => ∫ u in y..z,g u
  have hA z : HasDerivAt A (g z) z := intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable y z) hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hd x : HasDerivAt (fun z => A (φ z)-z) 0 x := by
    have hh := ((hA (φ x)).comp x (hφ x)).sub (hasDerivAt_id x)
    have hz : g (φ x)*f (φ x)-1=0 := by dsimp [g]; field_simp [hn (φ x)] <;> ring
    rw [hz] at hh
    convert hh using 1
    ext z
    rfl
  have he := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv)
  intro x
  have hh := he x 0
  dsimp only [A] at hh
  rw [h0,intervalIntegral.integral_same,sub_zero] at hh
  linarith

end Asakura.Chapter4
