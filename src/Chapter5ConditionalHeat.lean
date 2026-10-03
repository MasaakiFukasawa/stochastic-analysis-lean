import Chapter5IndependentAverage
import Chapter5LogHeat

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace Asakura.Chapter5
open Asakura.FullAudit
set_option maxHeartbeats 1600000

/-- The law of the scaled standard normal includes zero variance. -/
theorem gaussian_scaled_standard (s : ℝ) (hs : 0 ≤ s) :
    (gaussianReal 0 1).map (fun z => Real.sqrt s*z) = gaussianReal 0 s.toNNReal := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.eq
    simp [Real.sq_sqrt hs,Real.toNNReal_of_nonneg hs]

/-- Brownian independent increments turn the conditional payoff into the
same Gaussian integral used in the direct PDE calculation. -/
theorem conditional_heat_average
    {Ω : Type*} (G : MeasurableSpace Ω) {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (X Y : Ω → ℝ) (hX : Measurable[G] X) (hY : Measurable Y)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P)
    (s : ℝ) (hs : 0 ≤ s) (hlaw : P.map Y = gaussianReal 0 s.toNNReal)
    (f : ℝ → ℝ) (hf : Continuous f) (B : ℝ) (hb : ∀ x, ‖f x‖ ≤ B) :
    P[(fun w => f (X w+Y w))|G] =ᵐ[P] fun w => heatAverage f (X w) s := by
  have he := conditional_independent_bounded_average G P hG X Y hX hY hind
    (fun z : ℝ × ℝ => f (z.1+z.2)) (hf.measurable.comp (measurable_fst.add measurable_snd))
    B ((norm_nonneg (f 0)).trans (hb 0)) (fun z => hb _)
  filter_upwards [he] with w hw
  rw [hw,hlaw,← gaussian_scaled_standard s hs]
  exact integral_map (by fun_prop) (hf.comp (by fun_prop)).aestronglyMeasurable

/-- Taking the logarithm preserves the actual conditional-expectation
identity. Positivity of the Gaussian side follows separately from the
bounded exponential payoff and is used for Ito's formula. -/
theorem conditional_log_heat
    {Ω : Type*} (G : MeasurableSpace Ω) {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (hG : G ≤ m)
    (X Y : Ω → ℝ) (hX : Measurable[G] X) (hY : Measurable Y)
    (hind : Indep G (MeasurableSpace.comap Y inferInstance) P)
    (s : ℝ) (hs : 0 ≤ s) (hlaw : P.map Y = gaussianReal 0 s.toNNReal)
    (f : ℝ → ℝ) (hf : Continuous f) (a B : ℝ)
    (hb : ∀ x, ‖Real.exp (a*f x)‖ ≤ B) :
    (fun w => Real.log (P[(fun w => Real.exp (a*f (X w+Y w)))|G] w)/a) =ᵐ[P]
      fun w => logHeat a (fun x => Real.exp (a*f x)) (X w) s := by
  filter_upwards [conditional_heat_average G P hG X Y hX hY hind s hs hlaw
    (fun x => Real.exp (a*f x)) (Real.continuous_exp.comp (hf.const_mul a)) B hb] with w hw
  exact congrArg (fun z => Real.log z/a) hw

end Asakura.Chapter5
