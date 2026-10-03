import Chapter4PredictableBrownianIncrement
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace Asakura.Chapter7
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The square moment of a finite orthogonal family. This is applied to
predictable coefficients times successive Brownian increments. -/
theorem orthogonal_square_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s,MemLp (X i) 2 P)
    (horth : ∀ i ∈ s,∀ j ∈ s,i ≠ j → (∫ w,X i w*X j w ∂P)=0) :
    (∫ w,(∑ i ∈ s,X i w)^2 ∂P)=∑ i ∈ s,∫ w,(X i w)^2 ∂P := by
  classical
  simp_rw [pow_two,Finset.sum_mul_sum]
  have hip i hi j hj : Integrable (fun w => X i w*X j w) P := (hX i hi).integrable_mul (hX j hj)
  rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hip i hi j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => hip i hi j hj)]
  exact Finset.sum_eq_single_of_mem i hi (fun j hj hji => horth i hi j hj hji.symm)

/-- Independence from the current information kills cross terms with all
past measurable weights; the weights themselves need not be independent. -/
theorem independent_centered_cross {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (F : MeasurableSpace Ω) (Z U V : Ω → ℝ)
    (hi : Indep (MeasurableSpace.comap Z inferInstance) F P)
    (hU : Measurable[F] U) (hV : Measurable[F] V)
    (hZ : Integrable Z P) (hUV : Integrable (fun w => U w*V w) P)
    (hmean : (∫ w,Z w ∂P)=0) :
    (∫ w,U w*(V w*Z w) ∂P)=0 := by
  letI : MeasurableSpace Ω := m
  have hind : IndepFun Z (fun w => U w*V w) P :=  Asakura.Chapter4.indepFun_of_independent_information P F Z
    (fun w => U w*V w) hi (hU.mul hV)
  have he := hind.symm.integral_mul_eq_mul_integral hUV.aestronglyMeasurable hZ.aestronglyMeasurable
  simpa only [Pi.mul_apply,hmean,mul_zero,mul_assoc] using he

end Asakura.Chapter7
