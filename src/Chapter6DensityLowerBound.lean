import Chapter1WrittenJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace Asakura.Chapter6
open Asakura.Chapter1Written
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

/-- The final conditional-Jensen step in the density lower bound. -/
theorem exponential_conditional_lower_bound
    {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ m) (S V K L : Ω → ℝ)
    (hS : Integrable S P) (hV : Integrable V P)
    (hD : Integrable (fun w => Real.exp (S w-(1/2:ℝ)*V w)) P)
    (hs : ∀ᵐ w ∂P,-K w ≤ P[S|G] w) (hv : ∀ᵐ w ∂P,P[V|G] w ≤ L w) :
    ∀ᵐ w ∂P,Real.exp (-K w-L w/2) ≤ P[(fun w => Real.exp (S w-(1/2:ℝ)*V w))|G] w := by
  have hj := conditional_jensen_written hG convexOn_exp (hS.sub (hV.const_mul (1/2:ℝ))) hD
  have hc := condExp_sub hS (hV.const_mul (1/2:ℝ)) G
  have hm := condExp_smul (μ := P) (1/2:ℝ) V G
  filter_upwards [hj,hc,hm,hs,hv] with w hj hc hm hs hv
  apply le_trans _ hj
  apply Real.exp_le_exp.mpr
  rw [hc]
  change -K w-L w/2 ≤ P[S|G] w-P[(fun w => (1/2:ℝ)*V w)|G] w
  change P[(fun w => (1/2:ℝ)*V w)|G] w = (1/2:ℝ)*P[V|G] w at hm
  rw [hm]
  linarith

/-- A continuous positive lower bound valid a.e. for a continuous density
is valid at every point, because nonempty open sets have positive measure. -/
theorem continuous_density_strictly_positive
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsOpenPosMeasure ν]
    (p q : E → ℝ) (hp : Continuous p) (hq : Continuous q)
    (hpos : ∀ x,0 < q x) (hb : q ≤ᵐ[ν] p) : ∀ x,0 < p x := by
  have he : (fun x => max (q x) (p x)) = p :=
    eq_of_ae_eq (hb.mono fun x hx => max_eq_right hx) (hq.max hp) hp
  intro x
  have hh := congrFun he x
  exact (hpos x).trans_le (hh ▸ le_max_left (q x) (p x))

end Asakura.Chapter6
