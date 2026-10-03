import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory Set Filter
namespace Asakura.Chapter12
set_option backward.isDefEq.respectTransparency false

/-- Conditioning on a Brownian bridge leaves a strictly increasing function
of an atomless terminal Gaussian variable. Each level set therefore has
product measure zero. -/
theorem monotone_fiber_no_atoms {B : Type*} [MeasurableSpace B]
    (μ : Measure B) (ν : Measure ℝ) [SFinite μ] [SFinite ν] [NullSingletonClass ν]
    (A : B × ℝ → ℝ) (hA : Measurable A)
    (hmono : ∀ b, StrictMono (fun z => A (b,z))) (K : ℝ) :
    (μ.prod ν) {w | A w = K} = 0 := by
  have hm : MeasurableSet {w | A w = K} := hA (measurableSet_singleton K)
  rw [Measure.prod_apply hm]
  have hz (b : B) : ν (Prod.mk b ⁻¹' {w | A w = K}) = 0 := by
    apply Set.Countable.measure_zero
    apply Set.Subsingleton.countable
    intro x hx y hy
    exact (hmono b).injective (hx.trans hy.symm)
  simp only [hz,lintegral_zero]

/-- Transfer the preceding fiber argument to the original probability space
using the established joint law of bridge and terminal value. -/
theorem no_atom_from_bridge_terminal_law {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) (μ : Measure B) (ν : Measure ℝ)
    [SFinite μ] [SFinite ν] [NullSingletonClass ν]
    (Z : Ω → B × ℝ) (hZ : HasLaw Z (μ.prod ν) P)
    (A : B × ℝ → ℝ) (hA : Measurable A)
    (hmono : ∀ b, StrictMono (fun z => A (b,z))) (K : ℝ) :
    P {w | A (Z w) = K} = 0 := by
  have hm : MeasurableSet {w | A w = K} := hA (measurableSet_singleton K)
  have he := congrArg (fun m : Measure (B × ℝ) => m {w | A w = K}) hZ.map_eq
  rw [Measure.map_apply_of_aemeasurable hZ.aemeasurable hm] at he
  exact he.trans (monotone_fiber_no_atoms μ ν A hA hmono K)

end Asakura.Chapter12
